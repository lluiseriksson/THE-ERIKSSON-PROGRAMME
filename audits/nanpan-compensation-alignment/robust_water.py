"""Finite certificates for clipped payer shares in four-prefecture scenarios."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

def scenarios():
    rows=json.loads(Path('signed.json').read_bytes())
    return {a['calibration']+' / '+a['retention']:([F(x)/F(a['base_return']) for x in a['signed_payers']],list(map(F,a['benefit_shares']))) for a in rows if a.get('ratio') is not None}

def cells(data):
    cuts=[]
    for i in range(4):
        knots=sorted({F(0),F(1)}|{-r[i] for r,s in data.values() if -1<r[i]<0})
        cuts.append(list(zip(knots,knots[1:])))
    for box in product(*cuts):
        if sum(x for x,y in box)<=1<=sum(y for x,y in box):yield box

def coefficients(box,data):
    # (slope, constant) at tolerance zero plus tolerance times another affine row.
    for i,(lo,hi) in enumerate(box):
        unit=[int(k==i) for k in range(4)]
        yield ([-a for a in unit]+[lo],[0]*5)
        yield (unit+[-hi],[0]*5)
    for r,s in data.values():
        active=[int(r[i]+(lo+hi)/2>=0) for i,(lo,hi) in enumerate(box)]
        mass=active+[sum(v*a for v,a in zip(r,active))]
        for mask in range(1,15):
            inside=[int(mask>>i&1) for i in range(4)]
            share=sum(v*a for v,a in zip(s,inside))
            slope=[a*(bit-share) for a,bit in zip(active,inside)]
            yield (slope+[sum(v*a for v,a in zip(r,slope))],[-v for v in mass])

def loss(data,u):
    if min(u)<0 or sum(u)!=1:raise ValueError('Not a share vector')
    out={}
    for name,(r,s) in data.items():
        h=[max(F(0),a+b) for a,b in zip(r,u)]
        out[name]=sum(abs(v/sum(h)-t) for v,t in zip(h,s))/2
    return out

def replay(data,result):
    u=list(map(F,result['shares']));upper=max(loss(data,u).values())
    if upper!=F(result['upper']):raise ValueError('Objective witness')
    lower=F(result['lower'])
    boxes=list(cells(data))
    if lower==0:
        if result['exclusions']:raise ValueError('Unexpected lower certificate')
    else:
        if len(boxes)!=len(result['exclusions']):raise ValueError('Incomplete sign-cell coverage')
        for box,cert in zip(boxes,result['exclusions']):
            a=list(coefficients(box,data));total=[F(0)]*5
            for i,v in cert:
                if not (0<=i<len(a) and int(v)>0):raise ValueError('Invalid multiplier')
                p,h=a[i];total=[t+int(v)*(x+lower*y) for t,x,y in zip(total,p,h)]
            if total[-1]+min(total[:4])<=0:raise ValueError('Lower bound not proved on entire simplex')
    if not 0<=upper-lower<F(1,100000):raise ValueError('Uncertified precision')
    return float(lower),float(upper)

def solve(data):
    import numpy as np
    from scipy.optimize import linprog
    boxes=list(cells(data))
    arrays=[np.array(list(coefficients(box,data)),dtype=float) for box in boxes]
    def lp(arr,t):
        rows=arr[:,0,:]+float(t)*arr[:,1,:]
        result=linprog([0,0,0,0,1],A_ub=np.column_stack([rows[:,:4],-np.ones(len(rows))]),b_ub=-rows[:,4],A_eq=[[1,1,1,1,0]],b_eq=[1],bounds=[(None,None)]*5,method='highs')
        if not result.success:raise ValueError(result.message)
        return result
    u=[F(1,4)]*4;upper=max(loss(data,u).values());lo=0.;order=list(range(len(boxes)))
    for _ in range(29):
        t=(lo+float(upper))/2
        for i in order:
            p=lp(arrays[i],t)
            if p.fun<1e-9:
                approx=[F(max(0,round(v*10**10)),10**10) for v in p.x[:4]]
                v=[a/sum(approx) for a in approx];value=max(loss(data,v).values())
                if value<upper:
                    u,upper=v,value
                order=[i]+[j for j in order if j!=i]
                break
        else:lo=t
        if float(upper)-lo<1e-7:break
    lower=max(F(0),F(int(upper*10**6)-2,10**6))
    certs=[]
    if lower:
        for arr in arrays:
            p=lp(arr,lower)
            certs.append([[i,int(round(-v*10**12))] for i,v in enumerate(p.ineqlin.marginals) if round(-v*10**12)>0])
    res=dict(shares=list(map(str,u)),upper=str(upper),lower=str(lower),exclusions=certs,scenario_losses={k:float(v) for k,v in loss(data,u).items()})
    replay(data,res)
    return res

def groups(d):
    yield 'all',d
    for key in ('calibration','retention'):
        idx=0 if key=='calibration' else 1
        for group in sorted({s.split(' / ')[idx] for s in d}):
            yield key+': '+group,{s:v for s,v in d.items() if s.split(' / ')[idx]==group}
    for s,v in d.items():yield 'identified: '+s,{s:v}

if __name__=='__main__':
    print(json.dumps({name:solve(d) for name,d in groups(scenarios())},indent=2))