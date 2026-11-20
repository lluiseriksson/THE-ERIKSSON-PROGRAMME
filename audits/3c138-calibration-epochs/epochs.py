from pathlib import Path
import csv, io, json, hashlib, zipfile, math
from urllib.request import urlopen
from itertools import combinations
import numpy as np
from scipy.optimize import linprog
url='https://science.nrao.edu/facilities/vla/docs/manuals/obsguide/interp_user_table_0521-166-3c138_2025-03-06.csv'
raw=urlopen(url,timeout=45).read()
digest=hashlib.sha256(raw).hexdigest()
if digest!='ea19cb5f3152e2c4d1514afb9bffe737a77a970b7ee26b664c0bf0a2bd58565e':raise ValueError('Source changed')
rows=list(csv.DictReader(io.StringIO(raw.decode('utf-8-sig'))))
bands=['L','S','C','X','U','K','A','Q']
dates=[r['date'] for r in rows]
if len(set(dates))!=47 or dates!=sorted(dates) or (dates[0],dates[-1])!=('2021-02-01','2024-12-01'):raise ValueError('epoch set')
F=np.array([[float(r[b]) for b in bands] for r in rows])
if np.any(~np.isfinite(F)) or np.any(F<=0):raise ValueError('bad factor')
# Exact feasibility at a given tolerance via differences of band offsets.
from functools import lru_cache
L=np.log(F)
def segment_results(eps):
    limit=math.atanh(eps)
    @lru_cache(None)
    def check(i,end):
        logs=L[i:end]
        # Edge k -> j has weight bounding v[j]-v[k].
        W=(logs[:,:,None]-logs[:,None,:]).min(axis=0).T+2*limit
        D=W.copy()
        np.fill_diagonal(D,0)
        for k in range(len(bands)):
            D=np.minimum(D,D[:,k,None]+D[k,None,:])
        if D.diagonal().min() < -1e-10:return None
        v=D[0]
        R=logs-v
        u=(R.max(axis=1)+R.min(axis=1))/2
        ratios=np.exp(u[:,None]+v-logs)/math.cosh(limit)
        peak=float(np.max(abs(ratios-1)))
        if peak>eps+1e-9:raise ArithmeticError('band/date witness')
        return dict(start=dates[i],last=dates[end-1],max_abs_relative_error=peak,month_factor=(np.exp(u)/math.cosh(limit)).tolist(),band_shape=np.exp(v).tolist())
    N=len(dates);dp=[0]+[N+1]*N
    for j in range(1,N+1):
        dp[j]=min(dp[i]+1 for i in range(j) if check(i,j) is not None)
    groups=[];i=0
    while i<N:
        end=next((e-1 for e in range(i+1,N+1) if check(i,e) is None),N)
        if end<=i:raise ArithmeticError('one month infeasible')
        groups.append(check(i,end));i=end
    if len(groups)!=dp[-1]:raise ArithmeticError('dynamic program disagrees')
    return dict(tolerance=eps,minimum_shapes=int(dp[-1]),calendar=groups,dp_prefix_minima=dp)
res={str(eps):segment_results(eps) for eps in [.01,.02,.05,.10]}
# Independent LP on every maximal greedy segment and each failing one-month extension.
for key,r in res.items():
    eps=r['tolerance']
    for block in r['calendar']:
        i=dates.index(block['start']);end=dates.index(block['last'])+1
        for j in [end]+([end+1] if end<len(dates) else []):
            m,n=j-i,len(bands);X=np.zeros((m*n,m+n))
            for arow in range(m):
                for col in range(n):
                    index=arow*n+col;X[index,arow]=1;X[index,m+col]=1
            y=L[i:j].ravel();A=np.r_[X,-X]
            solution=linprog([0]*(m+n)+[1],A_ub=np.c_[A,-np.ones(len(A))],b_ub=np.r_[y,-y],bounds=[(0,0)]+[(None,None)]*(m+n-1)+[(0,None)],method='highs')
            if not solution.success:raise ValueError('LP')
            achieved=math.tanh(solution.x[-1])
            if (j==end and achieved>eps+1e-9) or (j>end and achieved<=eps+1e-9):raise ValueError('LP inconsistent with intervals')
            block['optimum' if j==end else 'with_next_month']=achieved
path=Path('/content/archive.zip')
with zipfile.ZipFile(path,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('epocas.json',json.dumps(dict(sha256=digest,by_tolerance=res),indent=2,allow_nan=False))
print('archive_sha256',hashlib.sha256(path.read_bytes()).hexdigest())
