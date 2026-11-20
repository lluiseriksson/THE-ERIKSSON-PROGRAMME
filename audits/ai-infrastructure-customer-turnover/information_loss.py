"""Exact disclosure ablations. Tables use percent units, and amounts use the filing's units."""
from fractions import Fraction as F
from pathlib import Path
import json

def check(ok,msg):
    if not ok: raise ValueError(msg)

def implied(t,h,q,ys,qs):
    d=F(1,2)
    return (((t-d)*(ys-d)-(q+d)*(qs+d))/(h+d),
            ((t+d)*(ys+d)-(q-d)*(qs-d))/(h-d))

def close_notes(vec, rows):
    for idx, value in rows.items():
        check(vec[idx]>=10 and abs(vec[idx]-value)<F(1,2),'rounding')
    check(max(v for k,v in enumerate(vec) if k not in rows)<10,'censoring')

def simple(mode, side, x):
    # First three entries are the June rows. Keep untouched zero labels for new customers.
    size=32
    a=[F(0)]*size;b=a.copy();first=a.copy()
    if side=='lower':
        a[:3]=[F(71,2)+x,F(51,2)+x,F(10)]
        b[:3]=[F(61,2)-x,F(49,2)-x,10-x]
        j,k=1,0   # September A and B
        for i in range(3,10):
            a[i]=(100-sum(a[:3]))/7
            b[i]=(100-sum(b[:3]))/7
    else:
        a[:3]=[F(36),F(26),F(10)]
        for i in range(3,10): a[i]=F(28,7)
        j,k=(0,11) if mode=='9M' else (10,11)
        b[j],b[k]=F(47,2)+x,F(30)
        for i in range(12,20): b[i]=(100-b[j]-b[k])/8
    if mode=='9M':
        for i,ys in [(j,33),(k,26)]:
            first[i]=(8314*ys-3661*b[i]-2575*a[i])/2078
    elif mode=='H1':
        for i,ys in [(0,40),(1,23)]:
            first[i]=(4653*ys-2575*a[i])/2078
    # Residual Q1 mass has fresh names; respecting the censored tail is checked below.
    remaining=100-sum(first)
    for i in range(20,32): first[i]=remaining/12
    h=[(2078*f+2575*v)/4653 for f,v in zip(first,a)]
    y=[(4653*g+3661*v)/8314 for g,v in zip(h,b)]
    for col in [first,a,b,h,y]:check(min(col)>=0 and sum(col)==100,'accounting')
    close_notes(a,{0:36,1:26,2:10});close_notes(b,{j:24,k:30})
    if mode=='H1':close_notes(h,{0:40,1:23})
    if mode=='9M':close_notes(y,{j:33,k:26})
    tv=sum(abs(v-z) for v,z in zip(a,b))/2
    goal=6+5*x if side=='lower' else F(153,2)-x if mode=='9M' else 100
    check(tv==goal,'unexpected endpoint')
    return dict(mode=mode,side=side,epsilon=str(x),turnover=str(tv),
                q1=list(map(str,first)),q2=list(map(str,a)),q3=list(map(str,b)))

def main():
    rows=[simple(m,s,F(1,e)) for m in ['quarter','H1','9M'] for s in ['lower','upper'] for e in [100,1000,10000]]
    from importlib.util import spec_from_file_location, module_from_spec
    p=spec_from_file_location('original',Path(__file__).with_name('sec-turnover-witness.py'));mod=module_from_spec(p);p.loader.exec_module(mod)
    both=[mod.witness(s,F(1,e)) for s in ['lower','upper'] for e in [100,1000,10000]]
    ranges={}
    for issuer,t,h,q,ys,qs,old in [('CoreWeave',8314,4653,3661,[33,26],[24,30],[40,23]),('Corvex',9294,4312,4982,[69,25],[72,23],[64,28])]:
        vals=[implied(t,h,q,a,b) for a,b in zip(ys,qs)]
        for i,(l,u) in enumerate(vals):
            check([j for j,v in enumerate(old) if max(l,v-F(1,2))<=min(u,v+F(1,2))]==[i],'links')
        ranges[issuer]=[list(map(str,tup)) for tup in vals]
        if issuer=='CoreWeave':check(min(v[0] for v in vals)>10,'hidden category possible')
        else:
            # The two known H1 shares sum to at least 91, leaving net residual at most 9.
            check(min(v[0] for v in vals)-9>16,'refund robustness insufficient')
    check(F(71,2)*(2575-F(1,2))>10*(8314+F(1,2)),'June leader can disappear from YTD9')
    print(json.dumps(dict(witnesses=rows,both=both,implied_H1_pct=ranges,closures={'Q2_Q3':[6,100],'plus_H1':[6,100],'plus_9M':[6,76.5],'both':[11,51]}),sort_keys=True))
if __name__=='__main__':main()

