"""Two correlation geometries compatible with every disclosed BRCA control-hit pair."""
import csv,json
from collections import defaultdict,Counter
from math import comb
from fractions import Fraction as F
from itertools import combinations
K=50;G=20211
def table(n):return list(csv.DictReader(open(n,encoding='utf-8-sig')))
summary=[r for r in table('bench_summary.csv') if r['cancer']=='BRCA']
panel=[r for r in table('bench_panel_genes.csv') if r['cancer']=='BRCA']
key=lambda r:'|'.join(r[k] for k in ['model','protocol','config'])
names=sorted({r['gene'] for r in panel});assert len(names)==12
# Deterministic labels for this existence certificate; these degrees are hypothetical.
low=names[:7];high=names[7:];deg={g:21 if g in low else 3000 for g in names}
def choose(n,k):return comb(n,k) if 0<=k<=n else 0
def indicator_block(n):
    return {(m,int(m>0)):comb(n,m) for m in range(min(K,n)+1)}
def combine(a,b):
    out=defaultdict(int)
    for (i,x),v in a.items():
        for (j,y),z in b.items():
            if i+j<=K:out[i+j,x+y]+=v*z
    return out
def dist(shared):
    p={(0,0):1};used=0
    for _ in high:p=combine(p,indicator_block(3000));used+=3000
    if not shared:
        for _ in low:p=combine(p,indicator_block(21));used+=21
    else:
        for n in (3,4):
            # Two private genes for each control (the control plus a copy).
            # If a common gene is drawn, all n neighborhoods in the block are hit.
            block={(0,0):1}
            for _ in range(n):block=combine(block,indicator_block(2))
            for j in range(1,min(K,19+2*n)+1):
                # Vandermonde: count draws of j with at least one of 19 shared genes.
                block[j,n]=block.get((j,n),0)+choose(19+2*n,j)-choose(2*n,j)
            p=combine(p,block);used+=19+2*n
    out=defaultdict(int)
    for (i,r),v in p.items():out[r]+=choose(G-used,K-i)*v
    assert sum(out.values())==comb(G,K)
    return {r:F(v,comb(G,K)) for r,v in out.items()}
def hit(n):return 1-F(comb(G-n,K),comb(G,K))
pack=lambda x:dict(num=x.numerator,den=x.denominator,approx=float(x))
means=sum(hit(n) for n in deg.values())
checks={}
for r in summary:
    k=key(r);rr=[z for z in panel if key(z)==k];direct={z['gene'] for z in rr if int(z['in_top50'])};want=int(r['recovery_proxy'])
    assert len(rr)==12 and len(direct)==int(r['recovery_top50'])<=want<=12
    # Labels below denote disjoint private gene IDs. Fill remaining positions
    # from a background clique orthogonal to all 12 controls in both constructions.
    more=sorted(set(names)-direct)[:want-len(direct)]
    choices=[('control',g) for g in sorted(direct)]+[('private',g) for g in more]+[('filler',str(i)) for i in range(K-want)]
    assert len(set(choices))==K and {g for t,g in choices if t=='control'}==direct
    recovered={g for t,g in choices if t!='filler'}
    assert len(recovered)==want
    checks[k]=dict(direct=sorted(direct),additional_private=more,proxy_hits=want)
actual={}
for shared,n in [(False,'disjoint'),(True,'shared')]:
    d=dist(shared);actual[n]=sum(p for r,p in d.items() if r>=8)
    assert sum(r*p for r,p in d.items())==means
upper=comb(7,3)*F(comb(K,3)*21**3,comb(G,3))
lower=hit(38)-5*(1-hit(3000))
assert actual['disjoint']<=upper<F(1,20)<lower<=actual['shared'] and len(checks)==16
print(json.dumps({'population':G,'draw':K,'control_sizes':deg,'checks':checks,'common_mean':pack(means),'tails':{k:pack(v) for k,v in actual.items()},'analytic_upper_disjoint':pack(upper),'analytic_lower_shared':pack(lower),'control_groups':[low[:3],low[3:],high]},sort_keys=True))
