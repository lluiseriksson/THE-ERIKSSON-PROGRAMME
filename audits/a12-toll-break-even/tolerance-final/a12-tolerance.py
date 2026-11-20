"""Exact certificates for positive rank-one approximation of A12 external charges."""
from pathlib import Path
from fractions import Fraction as F
import json,math
from itertools import product
import numpy as np
from scipy.optimize import brentq
from scipy.sparse.csgraph import floyd_warshall, NegativeCycleError
from sympy import Poly,Symbol,expand,factor,QQ
rows=json.loads(Path('sections.json').read_bytes())['profiles']
n=15
cols={(j,k):[F(y[k]) for y in data] for j,data in rows.items() for k in [1,2] if max(F(y[k]) for y in data)>0}
order=list(cols); z=np.array([[float(y) for y in cols[p]] for p in order])
def exact(e,subset):
    edges={}
    for i,j in product(range(n),repeat=2):
        if i==j:continue
        edges[i,j]=min(((cols[p][j]+e)/(cols[p][i]-e),p) for p in subset if cols[p][i]>e)
    d=[F(1)]*n;pred={}
    for _ in range(n):
        last=None
        for (i,j),(w,p) in edges.items():
            if d[i]*w<d[j]:d[j]=d[i]*w;pred[j]=(i,j,p);last=j
        if last is None:
            rates={p:max((a-e)/b for a,b in zip(cols[p],d)) for p in subset}
            assert all(abs(a-rates[p]*l)<=e for p in subset for a,l in zip(cols[p],d))
            return dict(feasible=True,lengths=list(map(str,d)),rates={j+':'+str(k):str(v) for (j,k),v in rates.items()})
    for _ in range(n):last=pred[last][0]
    start=last;cycle=[]
    while True:
        i,j,p=pred[last];cycle.append([i,j,list(p)]);last=i
        if last==start:break
    assert math.prod((cols[tuple(p)][j]+e)/(cols[tuple(p)][i]-e) for i,j,p in cycle)<1
    return dict(feasible=False,cycle=cycle[::-1])
def fit(subset):
    a=z[[order.index(p) for p in subset]]
    def numeric(e):
        x=np.min(np.log(a[:,None,:]+e)-np.log(a[:,:,None]-e),axis=0)
        np.fill_diagonal(x,0)
        try:floyd_warshall(x,directed=True);return True
        except NegativeCycleError:return False
    lo=0;hi=0.0002
    # Float result selects trial tolerances only.
    for _ in range(39):
        m=(lo+hi)/2
        if numeric(m):hi=m
        else:lo=m
    scale=10**12
    a0=F(math.floor(lo*scale)-2,scale);b0=F(math.ceil(hi*scale)+2,scale)
    neg=exact(a0,subset);pos=exact(b0,subset)
    assert not neg['feasible'] and pos['feasible']
    x=Symbol('t');cycle=neg['cycle']
    eq=Poly(math.prod(cols[tuple(p)][j]+x for i,j,p in cycle)-math.prod(cols[tuple(p)][i]-x for i,j,p in cycle),x,domain=QQ)
    assert eq.eval(a0)<0 and eq.eval(b0)>=0
    rational=[F(q) for q in eq.ground_roots() if a0<=q<=b0]
    point=None
    if len(rational)==1:
        test=exact(rational[0],subset)
        if test['feasible']:point=str(rational[0]);pos=test;b0=rational[0]
    return dict(lower=str(a0),upper=str(b0),point=point,lower_witness=neg,upper_witness=pos,cycle_equation=str(factor(eq.as_expr())),coefficients=list(map(str,eq.all_coeffs())))
original=F(137,2513200)
out={'prior_tolerance':str(original),'prior_test':exact(original,order),'designs':{}}
for k,subset in [('air',[p for p in order if p[1]==1]),('carbon',[p for p in order if p[1]==2]),('both',order)]:out['designs'][k]=fit(subset)
print(json.dumps(out,indent=2))