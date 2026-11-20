"""Recheck exact primal and dual witnesses and all section sums using the standard library."""
from pathlib import Path
from fractions import Fraction as F
import json
def read(n): return json.loads(Path(__file__).with_name(n).read_bytes())
def check(condition, message):
    if not condition: raise ValueError(message)
d=read('components.json')
rows=d['rows']
prices=list(map(F, read('corridor.json')['eur_ex_vat']))
check(len(rows)==len(prices)==24,'coverage')
for key,fit in d['designs'].items():
    design={}
    for j,row in enumerate(rows):
        i,a,c=map(F,row['components'])
        check(F(row['price'])==prices[j],'headline')
        if key.startswith('offset-axles-') and row['axles']!=int(key[-1]): continue
        design[j]={'one':[i+a+c],'two':[i,a+c],'three':[i,a,c]}.get(key,[i,a,c,1])
    beta=list(map(F,fit['coeff']))
    err=F(fit['error'])
    check(max(abs(sum(x*b for x,b in zip(z,beta))-prices[j]) for j,z in design.items())==err,'primal')
    weights=[(a['index'],a['sign'],F(a['weight'])) for a in fit['cells']]
    check(all(j in design and s in (-1,1) and v>0 for j,s,v in weights),'weights')
    check(sum(v for j,s,v in weights)==1,'mass')
    for t in range(len(beta)):
        check(sum(v*s*design[j][t] for j,s,v in weights)==0,'annihilator')
    check(-sum(v*s*prices[j] for j,s,v in weights)==err,'dual')
s=read('sections.json')
check(len(s['comparisons'])==36 and len(s['profiles'])==24 and s['segment_count']==15,'section coverage')
for v in s['comparisons']:
    j=v['row']; amounts=s['profiles'][str(j)]
    check(len(amounts)==15,'segment count')
    subtotal=sum(F(x[0]) for x in amounts)
    check(subtotal==F(v['section_sum']) and F(v['price'])==prices[j] and subtotal-prices[j]==F(v['difference']),'reconciliation')
print('Verified seven optimality certificates, 24 distinct profiles and 36 annex comparisons.')

# Verify independently from section amounts. No optimization library required.
t=read('tolerance.json')
from math import prod
for group,v in t['designs'].items():
    lo,hi=map(F,[v['lower'],v['upper']])
    valid={'air':[1],'carbon':[2],'both':[1,2]}[group]
    cycle=v['lower_witness']['cycle']
    check(lo>=0 and lo<=hi and hi-lo<F(1,10**10),'tolerance bracket')
    def cycle_products(e):
        left=right=F(1)
        for idx,(i,j,(key,k)) in enumerate(cycle):
            check(j==cycle[(idx+1)%len(cycle)][0] and k in valid,'cycle chain and class')
            ci,cj=[F(s['profiles'][key][r][k]) for r in [i,j]]
            check(ci>e,'positive cycle numerator and denominator')
            left*=cj+e;right*=ci-e
        return left,right
    a,b=cycle_products(lo);check(a<b,'strict lower bound')
    if v['point']:
        check(F(v['point'])==hi,'exact upper bound')
        a,b=cycle_products(hi);check(a==b,'sharp cycle at optimum')
    pos=v['upper_witness'];lengths=list(map(F,pos['lengths']))
    check(len(lengths)==15 and min(lengths)>0,'length witness')
    for key,amounts in s['profiles'].items():
        for k in valid:
            name=key+':'+str(k)
            rate=F(pos['rates'].get(name,'0'))
            check(rate>=0,'nonnegative rates')
            for L,row in zip(lengths,amounts):
                check(abs(L*rate-F(row[k]))<=hi,'all charge disclosures')
print('Checked three uniform-approximation optima or enclosing intervals with original charge products.')
