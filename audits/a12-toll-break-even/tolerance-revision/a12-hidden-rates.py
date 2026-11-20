"""Test common section lengths at unrestricted, globally stable class-specific rates."""
from fractions import Fraction as F
from pathlib import Path
import json
s=json.loads(Path('sections.json').read_bytes())
tol=F(1,20000)
def audit(parts, count):
    edges=[];zero=[]
    for j,amounts in s['profiles'].items():
        for k in parts:
            charges=[F(z[k]) for z in amounts[:count]]
            if max(charges)==0:
                zero.append([j,k]);continue
            inv='inv:'+j+':'+str(k)
            for i,v in enumerate(charges):
                length='L:'+str(i);edges.append((inv,length,v+tol))
                if v>tol:edges.append((length,inv,1/(v-tol)))
    names=sorted({n for a,b,g in edges for n in [a,b]})
    d={n:F(1) for n in names};parent={}
    for _ in names:
        final=None
        for a,b,g in edges:
            if d[b]>d[a]*g:
                d[b]=d[a]*g;parent[b]=(a,b,g);final=b
        if final is None:
            for a,b,g in edges:
                if d[b]>d[a]*g:raise RuntimeError('Invalid witness')
            return dict(feasible=True,zero_rates=zero,values={k:str(v) for k,v in d.items()})
    for _ in names:final=parent[final][0]
    start=final;cycle=[];product=F(1)
    while True:
        a,b,g=parent[final];cycle.append([a,b,str(g)]);product*=g;final=a
        if final==start:break
    if product>=1:raise RuntimeError('Invalid cycle')
    return dict(feasible=False,cycle=cycle[::-1],product=str(product))
out={str(n)+'-'+label:audit(cols,n) for n in [14,15] for label,cols in [('air',[1]),('carbon',[2]),('both',[1,2])]}
print(json.dumps(out,indent=2))