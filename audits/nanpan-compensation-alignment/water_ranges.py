"""Certified marginal range of each prefecture's surcharge within a fixed loss threshold."""
from fractions import Fraction as F
from pathlib import Path
import json
from robust_water import cells,coefficients,scenarios,loss
NAMES=['Kunming','Yuxi','Honghe','Wenshan']
LEVEL=F(24752,100000)
def rows(box,d):
    return [[x+LEVEL*y for x,y in zip(p,h)] for p,h in coefficients(box,d)]
def weights(v):
    return [[i,int(round(-a*10**10))] for i,a in enumerate(v) if round(-a*10**10)>0]
def combine(a,certificate):
    t=[F(0)]*5
    for i,w in certificate:
        if not (0<=i<len(a) and isinstance(w,int) and w>0):raise ValueError('Nonpositive multiplier')
        t=[x+w*y for x,y in zip(t,a[i])]
    return t
def replay(result):
    d=scenarios();boxes=list(cells(d))
    if F(result['level'])!=LEVEL:raise ValueError('Wrong tolerance')
    bounds=[]
    for i,name in enumerate(NAMES):
        interval=[]
        for sign in (1,-1):
            v=result[name][str(sign)];u=list(map(F,v['u']));inside=sign*u[i]
            if max(loss(d,u).values())>LEVEL:raise ValueError('Bad witness')
            if len(boxes)!=len(v['boxes']):raise ValueError('Missing boxes')
            outer=[]
            for box,entry in zip(boxes,v['boxes']):
                t=combine(rows(box,d),entry['weights'])
                if entry['type']=='empty':
                    if min(t[:4])+t[4]<=0:raise ValueError('Bad exclusion')
                else:
                    slope=[z/F(10**10)+sign*int(k==i) for k,z in enumerate(t[:4])]
                    outer.append(min(slope)+t[4]/F(10**10))
            bound=min(outer)
            if not 0<=inside-bound<F(1,100000):raise ValueError('Range gap')
            interval.append((float(sign*inside),float(sign*bound)))
        bounds.append(interval)
    return bounds
def solve():
    import numpy as np
    from scipy.optimize import linprog
    d=scenarios();boxes=list(cells(d));result={'level':str(LEVEL)}
    def lp(c,M,b):
        return linprog(c,A_ub=M,b_ub=b,A_eq=[[1,1,1,1]+([0] if len(c)==5 else [])],b_eq=[1],bounds=[(None,None)]*len(c),method='highs')
    arrays=[]
    for box in boxes:
        a=np.array(rows(box,d),dtype=float);M=a[:,:4];b=-a[:,4]
        slack=lp([0,0,0,0,1],np.column_stack([M,-np.ones(len(M))]),b)
        if not slack.success:raise ValueError(slack.message)
        arrays.append((M,b,weights(slack.ineqlin.marginals) if slack.fun>1e-9 else None))
    def rational(x):
        v=[F(max(0,round(s*10**12)),10**12) for s in x];return [a/sum(v) for a in v]
    for i,name in enumerate(NAMES):
        result[name]={}
        for sign in (1,-1):
            c=[sign*int(i==k) for k in range(4)]
            best=F(2);proof=[];witness=None
            for M,b,empty in arrays:
                if empty:
                    proof.append({'type':'empty','weights':empty});continue
                p=lp(c,M,b)
                if not p.success:raise ValueError(p.message)
                proof.append({'type':'bound','weights':weights(p.ineqlin.marginals)})
                if sign*p.x[i]>float(best)+1e-8:continue
                # Search just inside the polytope when a rounded boundary point is outside.
                for margin in (0,1e-11,1e-10,1e-9,1e-8):
                    bt=b.copy();bt[8:]-=margin
                    pp=lp(c,M,bt); 
                    if not pp.success:continue
                    u=rational(pp.x)
                    if max(loss(d,u).values())<=LEVEL:
                        if sign*u[i]<best:best,witness=sign*u[i],u
                        break
            if witness is None:raise ValueError('Missing rational witness')
            result[name][str(sign)]={'u':list(map(str,witness)),'boxes':proof}
    result['bounds']=replay(result)
    return result
if __name__=='__main__':print(json.dumps(solve(),indent=2))