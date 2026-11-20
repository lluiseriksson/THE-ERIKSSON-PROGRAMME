"""Audit table 2, column 4 on a fixed sample. Python implementation of within 2SLS."""
from pathlib import Path
from urllib.request import urlopen
import hashlib,io,json,zipfile
import numpy as np
import pandas as pd

def check(ok,why):
    if not ok:raise ValueError(why)
url='https://zenodo.org/api/records/20114638/files/Replication%20-%20VI.zip/content'
raw=urlopen(url,timeout=120).read()
digest=hashlib.sha256(raw).hexdigest()
check(digest=='ea56e8561cf45359707c2e2e65926701caca4b2821372567b9d5da4573aeb648','archive checksum')
with zipfile.ZipFile(io.BytesIO(raw)) as z:
    base='Replication - VI/'
    d=pd.read_stata(io.BytesIO(z.read(base+'Data/panel_final.dta')),convert_categoricals=False)
    lines=z.read(base+'Code/table_2.do').decode('latin1').splitlines()
    table=z.read(base+'Tabfig/table_2.txt').decode('latin1')
    source={str(i):lines[i-1] for i in [56,75,76,89,91,92,234,235]}
    check('0.247' in table and '0.48' in table,'target version')
for name in ('litall','missment_1','destgy4t_1','sexratio3060'):
    x=d[name].astype(float)
    d['z_'+name]=(x-x.mean())/x.std(ddof=1)
d['interaction']=d.z_sexratio3060*d.z_destgy4t_1
cols=['vcode','year','z_litall','z_missment_1','z_destgy4t_1','interaction','poptotalt_2','litallt_2']
sample=d.loc[d.year.between(1900,1930),cols].dropna().sort_values(['vcode','year']).copy()
check(not sample.duplicated(['vcode','year']).any(),'duplicate key')
groups=sample.vcode.to_numpy()
years=sample.year.to_numpy()
check(len(sample)==1284 and len(np.unique(groups))==321 and np.all(sample.groupby('vcode').size()==4),'sample mismatch')
# Demean within municipalities before projecting the remaining controls and year effects.
values=sample[cols[2:]].astype(float)
within=(values-values.groupby(sample.vcode).transform('mean')).to_numpy()
time=pd.get_dummies(sample.year,dtype=float).iloc[:,1:]
time=(time-time.groupby(sample.vcode).transform('mean')).to_numpy()
W=np.c_[within[:,4:],time]
# District identification and restricted wild-cluster bootstrap, null beta = 0.
from scipy.stats import chi2, beta as beta_dist
from threadpoolctl import threadpool_limits
district=d.loc[sample.index,'partycode']
check(district.notna().all() and district.groupby(sample.vcode).nunique().eq(1).all(),'unstable district')
with zipfile.ZipFile(io.BytesIO(raw)) as z:
    with pd.io.stata.StataReader(io.BytesIO(z.read(base+'Data/panel_final.dta'))) as sr:
        label=sr.variable_labels().get('partycode')
N=len(sample); B=9999; seed=20261120
y0=within[:,0]
W=W/np.linalg.norm(W,axis=0)
e0=y0-W@np.linalg.lstsq(W,y0,rcond=None)[0]
def one(k,group):
    unique,idx,n=np.unique(group,return_inverse=True,return_counts=True)
    G=len(unique)
    check(G>k+5 and n.sum()==N,'group support')
    Z=within[:,2:2+k]
    X=np.c_[W,Z/np.linalg.norm(Z,axis=0)]
    check(np.linalg.matrix_rank(X)==X.shape[1],'design rank')
    gram=np.linalg.inv(X.T@X)
    restriction=gram[-k:]
    # Signs are constant within municipalities under either grouping.
    # Fitted nuisance means can be dropped because their tested coefficients are zero.
    T=np.array([X[idx==i].T@e0[idx==i] for i in range(G)])
    H=np.array([X[idx==i].T@X[idx==i] for i in range(G)])
    def batch(S):
        coefs=(S@T)@gram
        scores=S[:,:,None]*T[None,:,:]-np.einsum('gij,bj->bgi',H,coefs)
        selected=scores@restriction.T
        cov=selected.transpose(0,2,1)@selected
        test=coefs[:,-k:]
        return np.sum(test*np.linalg.solve(cov,test[:,:,None])[:,:,0],axis=1)
    def direct(sign):
        y=e0*sign[idx]
        bfit=np.linalg.lstsq(X,y,rcond=None)[0]
        score=np.zeros((G,X.shape[1]))
        np.add.at(score,idx,X*(y-X@bfit)[:,None])
        z=score@restriction.T
        return float(bfit[-k:]@np.linalg.solve(z.T@z,bfit[-k:]))
    observed=direct(np.ones(G))
    check(np.isclose(observed,batch(np.ones((1,G)))[0],rtol=1e-9),'observed cross check')
    rng=np.random.default_rng(seed);hits=0;count=0
    for begin in range(0,B,100):
        S=2*rng.integers(0,2,size=(min(100,B-begin),G))-1
        vals=batch(S)
        check(np.isfinite(vals).all(),'undefined statistic')
        if begin==0:
            for j in range(5):check(np.isclose(vals[j],direct(S[j]),rtol=2e-8,atol=1e-10),'bootstrap cross check')
        hits+=int(np.sum(vals>=observed-1e-12));count+=len(S)
    check(count==B and 0<hits<B,'bootstrap count')
    return dict(groups=G,min_municipalities=int(min(n)//4),max_municipalities=int(max(n)//4),
        sizes_municipalities=[int(x//4) for x in n],wald=observed,asymptotic_p=float(chi2.sf(observed,k)),
        bootstrap_p=(hits+1)/(B+1),exceedances=hits,draws=B,seed=seed,
        mc95=[float(beta_dist.ppf(.025,hits,B-hits+1)),float(beta_dist.ppf(.975,hits+1,B-hits))])
with threadpool_limits(limits=1):
    tests={name:{str(k):one(k,group) for k in (1,2)} for name,group in [('municipality',groups),('district',district.to_numpy())]}
check(np.isclose(tests['municipality']['1']['asymptotic_p'],.06769378667269516,atol=1e-9),'municipal baseline')
report=dict(tests=tests,archive_sha256=digest,variable_label=label,observations=N,method='restricted Rademacher wild cluster bootstrap of reduced-form Wald, CR0, plus-one p, no leverage correction')
f=Path('/content/archive.zip')
with zipfile.ZipFile(f,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('districts.json',json.dumps(report,indent=2,allow_nan=False))
print('archive_sha256',hashlib.sha256(f.read_bytes()).hexdigest())
