"""Exact uniform-approximation certificates for the 2026 A12 corridor."""
from fractions import Fraction as F
from pathlib import Path
import itertools,json,hashlib
import numpy as np
from scipy.optimize import linprog
from sympy import Matrix
def read(n):return json.loads(Path(n).read_bytes())
def rate(v,component,r):
    euro={'emissionsfrei':'6','EURO VI':'6','EURO V / EEV':'5','EURO IV':'4','EURO 0 - III':'3'}[r['euro']]
    attr=dict(co2_class=r['co2'],euro_class=euro,train_axles=r['axles'],train_mass_kg=18000)
    def matches(test):
        for k,a in test.items():
            x=attr[k]
            if isinstance(a,dict):
                if not a.get('min',x)<=x<=a.get('max',x):return False
            elif x not in a:return False
        return True
    cl,=[x['id'] for cs in v['vehicle_class_sets'] if cs['id']==component+'-1' for x in cs['classes'] if matches(x['criteria'])]
    price,=[p for t in v['charges'] if t['id']==component for obj,g,p in t['rows'] if obj=='roads' and g==cl]
    return F(price)
def certificate(X,y,ids):
    d=len(X[0])
    mats=[[*[s*a for a in row],-1] for s in [1,-1] for row in X]
    rhs=[s*p for s in [1,-1] for p in y]
    objective=[0]*d+[1]
    lp=linprog(objective,A_ub=np.array(mats,float),b_ub=np.array(rhs,float),bounds=[(None,None)]*(d+1),method='highs')
    if not lp.success:raise RuntimeError(lp.message)
    active=np.flatnonzero(lp.ineqlin.residual<1e-7).tolist()
    for basis in itertools.combinations(active,d+1):
        M=Matrix([mats[j] for j in basis])
        if M.det()==0:continue
        solution=list(map(F,M.inv()*Matrix([rhs[j] for j in basis])))
        dual=list(map(F,-M.T.inv()*Matrix(objective)))
        if min(dual)>=0 and all(sum(a*b for a,b in zip(row,solution))<=h for row,h in zip(mats,rhs)):break
    else:raise ValueError(('No exact basis',ids,active))
    error=solution[-1]
    if error!=-sum(t*rhs[j] for t,j in zip(dual,basis)):raise ValueError('Dual objective')
    return dict(coeff=list(map(str,solution[:-1])),error=str(error),cells=[dict(index=ids[j%len(ids)],sign=1 if j<len(ids) else -1,weight=str(t)) for t,j in zip(dual,basis) if t])
v=read('at.json');rows=read('threshold.json')['rows'];P=list(map(F,read('corridor.json')['eur_ex_vat']));A=[];data=[]
for r,p in zip(rows,P):
    i,a,c=[rate(v,k,r) for k in ['infrastructure','air_noise','co2']]
    if i+a+c!=F(r['base']) or i!=F(r['infrastructure']):raise ValueError('Source components')
    A.append([5*i/4,a,c]);data.append(dict(axles=r['axles'],euro=r['euro'],co2=r['co2'],components=list(map(str,A[-1])),price=str(p)))
designs={}
for name,X in [('one',[[sum(z)] for z in A]),('two',[[i,a+c] for i,a,c in A]),('three',A),('three-plus-offset',[z+[F(1)] for z in A])]:
    cert=certificate(X,P,list(range(len(A))))
    designs[name]=cert
for n in [2,3,4]:
    ix=[j for j,r in enumerate(rows) if r['axles']==n]
    designs['offset-axles-'+str(n)]=certificate([A[j]+[F(1)] for j in ix],[P[j] for j in ix],ix)
if F(designs['one']['error'])!=F(read('corridor.json')['minimax_eur']):raise ValueError('Baseline mismatch')
print(json.dumps(dict(rows=data,designs=designs),indent=2))