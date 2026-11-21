"""Reconstruct mineral surfaces from published mean responses; distances in g per 100 g."""
import json, re, zipfile
import numpy as np
from scipy.optimize import linprog
with zipfile.ZipFile('tables.zip') as source:
    data=json.loads(source.read('index.json'))
assert data['sha256']=='e556708e9405fee2e72d1df8f7aeeaaa54979f617f6362f14b1aa4719bf56fb5'
pages=data['pages']
design={}
response={}
for line in pages['4'].splitlines():
    match=re.search(r'\bF(\d+)\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)\s*$',line)
    if match:
        design[int(match[1])]=[float(x) for x in match.groups()[1:]]
for line in (pages['10']+'\n'+pages['11']).splitlines():
    match=re.match(r'\s*F(\d+)\s+(.*)',line)
    if match:
        means=re.findall(r'(\d+\.\d+)\s*±',match[2])
        assert len(means)==4
        response[int(match[1])]=[float(x) for x in means[:3]]
assert sorted(design)==sorted(response)==list(range(1,20))
X=np.array([design[i] for i in sorted(design)])
Y=np.array([response[i] for i in sorted(design)])
assert np.allclose(X.sum(axis=1),100)
coef,_,rank,_=np.linalg.lstsq(X,Y,rcond=None)
assert rank==3
thresholds=[3,160,2.2]
printed=np.array([24.50,41.83,33.65])
centers=[100*printed/printed.sum()]+[printed+0.02*e for e in np.eye(3)]
def radius(center,a,target):
    # Minimize half the L1 distance using auxiliary absolute deviations.
    I=np.eye(3)
    A=np.vstack([np.c_[I,-I],np.c_[-I,-I],np.r_[a,np.zeros(3)]])
    sol=linprog([0,0,0,.5,.5,.5],A_ub=A,b_ub=np.r_[center,-center,target],A_eq=[[1,1,1,0,0,0]],b_eq=[100],bounds=[(10,80)]*3+[(0,None)]*3,method='highs')
    if sol.status==2:
        assert min(10*a.sum()+70*a)>target
        return None
    assert sol.success and abs(a@sol.x[:3]-target)<1e-7
    formula=(center@a-target)/(max(a)-min(a))
    witness=center.copy()
    witness[np.argmax(a)]-=formula
    witness[np.argmin(a)]+=formula
    assert min(witness)>=10 and max(witness)<=80 and abs(formula-sol.fun)<1e-8
    return dict(distance=float(sol.fun),witness=witness.tolist())
out=[]
for c in centers:
    out.append(dict(center=c.tolist(),predicted=(c@coef).tolist(),margins=[radius(c,a,t) for a,t in zip(coef.T,thresholds)]))
print(json.dumps(dict(order=['iron','calcium','zinc'],units='printed dry matter basis per 100 g; distance in g of flour per 100 g',fits=coef.tolist(),R2=(1-np.sum((Y-X@coef)**2,axis=0)/np.sum((Y-Y.mean(axis=0))**2,axis=0)).tolist(),references=[4.11,162.56,2.36],scenario_results=out,scope='Unweighted reconstruction from rounded Tables 1 and 3. Four declared mass closures, with no assumption of a distribution of between-source variation.')))