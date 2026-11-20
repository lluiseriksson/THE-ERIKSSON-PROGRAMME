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
def fit(A,ds,bs):
    m,n=A.shape
    y=np.log(A).ravel()
    X=np.zeros((m*n,m+n))
    for i in range(m):
        for j in range(n):
            X[i*n+j,i]=1
            X[i*n+j,m+j]=1
    H=np.vstack([X,-X]);M=np.column_stack([H,-np.ones(2*m*n)])
    result=linprog([0]*(m+n)+[1],A_ub=M,b_ub=np.r_[y,-y],bounds=[(0,0)]+[(None,None)]*(m+n-1)+[(0,None)],method='highs')
    if not result.success:raise ValueError(result.message)
    u,v,t=result.x[:m],result.x[m:m+n],result.x[-1]
    attained=np.max(np.abs(np.log(A)-u[:,None]-v))
    if abs(attained-t)>1e-9:raise ValueError('witness upper bound')
    L=np.log(A)
    best=(-1,None)
    for j,k in combinations(range(n),2):
        contrast=L[:,j]-L[:,k];a,b=int(contrast.argmax()),int(contrast.argmin())
        lower=float((contrast[a]-contrast[b])/4)
        if lower>best[0]:best=(lower,dict(dates=[ds[a],ds[b]],bands=[bs[j],bs[k]],factors=[[A[a,j],A[a,k]],[A[b,j],A[b,k]]]))
    if abs(best[0]-t)>1e-8:raise ValueError('Four-corner witness incomplete; retain and investigate longer cycles')
    fac=math.exp(t)
    min_relative=math.tanh(t)
    # Center the multiplicative interval about one for symmetric ordinary fractional error.
    scaled=np.exp(u[:,None]+v)/A/math.cosh(t)
    if abs(np.max(abs(scaled-1))-min_relative)>1e-8:raise ValueError('relative-error witness')
    return dict(dates=[ds[0],ds[-1]],bands=bs,log_optimum=t,factor=fac,min_max_abs_fractional_error=min_relative,four_corner_certificate=best[1],factor_by_date=np.exp(u).tolist(),base_by_band=np.exp(v).tolist(),max_certificate_gap=abs(best[0]-t))
cases={}
for title,selector,cols in [('all',slice(None),bands),('2024',slice(-12,None),bands),('L-through-X',slice(None),bands[:4]),('K-through-Q',slice(None),bands[-3:])]:
    ix=[bands.index(x) for x in cols]
    cases[title]=fit(F[selector][:,ix],dates[selector],cols)
report=dict(source=url,sha256=digest,months=len(rows),bands=bands,cases=cases,metric='ordinary fractional error is abs(approximation / tabulated - 1); log metric permits reciprocal bounds')
path=Path('/content/archive.zip')
with zipfile.ZipFile(path,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('certificado.json',json.dumps(report,indent=2,allow_nan=False))
print('archive_sha256',hashlib.sha256(path.read_bytes()).hexdigest())
