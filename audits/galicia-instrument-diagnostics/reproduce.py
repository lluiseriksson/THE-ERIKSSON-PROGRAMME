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
def estimates(keep):
    A=W[keep]
    R=within[keep,:4]-A@np.linalg.lstsq(A,within[keep,:4],rcond=None)[0]
    y,x=R[:,0],R[:,1]
    out={}
    for k,name in [(1,'single'),(2,'joint')]:
        Z=R[:,2:2+k]
        check(np.linalg.matrix_rank(Z)==k,'instrument rank')
        fitted=Z@np.linalg.lstsq(Z,x,rcond=None)[0]
        den=fitted@x
        check(den>0 and np.isclose(den,fitted@fitted),'first-stage projection')
        beta=float((fitted@y)/den)
        # Exact RMS outcome perturbation required for the point estimate to reach zero.
        rms=float(abs(beta)*np.linalg.norm(fitted)/np.sqrt(len(x)))
        out[name]=dict(beta=beta,excluded_instruments=k,overid_df=k-1,partial_r_squared=float(den/(x@x)),minimum_outcome_rms=rms)
    return out
full=estimates(np.ones(len(sample),dtype=bool))
deletions={}
for gi in np.unique(groups):
    rr=estimates(groups!=gi)
    deletions[str(int(gi))]=[rr['single']['beta'],rr['joint']['beta']]
bounds=np.array(list(deletions.values()))
result=dict(doi='10.5281/zenodo.20114638',archive_sha256=digest,source_lines=source,sample_n=len(sample),municipalities=len(deletions),years=sorted(set(map(int,years))),full=full,published_in_package=0.247,matches_at_printed_precision=(round(full['single']['beta'],3)==0.247),deletion_range=[bounds.min(axis=0).tolist(),bounds.max(axis=0).tolist()],deletions=deletions)
# Test candidate structural coefficients by regressing Y-bX on the excluded instruments
# after removing the controls. Use the cluster score covariance with no small-sample multiplier.
from scipy.stats import chi2
R=within[:,:4]-W@np.linalg.lstsq(W,within[:,:4],rcond=None)[0]
y,x=R[:,0],R[:,1]
cells=np.unique(groups,return_inverse=True)[1]
report={}
for name,k in [('single',1),('joint',2)]:
    Z=R[:,2:2+k]
    target=np.c_[y,x]
    params=np.linalg.solve(Z.T@Z,Z.T@target)
    errors=target-Z@params
    scores=np.zeros((len(set(cells)),k,2))
    np.add.at(scores,cells,Z[:,:,None]*errors[:,None,:])
    m=Z.T@target
    def wald(beta):
        s=scores[:,:,0]-beta*scores[:,:,1]
        t=m[:,0]-beta*m[:,1]
        return float(t@np.linalg.solve(s.T@s,t))
    first_scores=scores[:,:,1]
    first=float(m[:,1]@np.linalg.solve(first_scores.T@first_scores,m[:,1]))
    null=wald(0)
    report[name]=dict(ar_null_chi2=null,ar_null_df=k,ar_null_p=float(chi2.sf(null,k)),first_stage_wald_chi2=first,first_stage_wald_per_restriction=first/k,cluster_covariance='CR0, no small-sample multiplier',overidentification_degrees=k-1,clusters=len(set(cells)))
    # Direct dummy-regression cross check for the null on the identical rows.
    dummy=pd.get_dummies(sample.vcode,dtype=float).to_numpy()
    design=np.c_[dummy,time,values.iloc[:,4:],values.iloc[:,2:2+k]]
    rawy=values.iloc[:,0].to_numpy();coef=np.linalg.lstsq(design,rawy,rcond=None)[0]
    residual=rawy-design@coef
    check(np.max(np.abs(residual-errors[:,0]))<2e-6,'dummy fit differs')
    check(np.isclose(wald(full[name]['beta']),0,atol=1e-8) if k==1 else True,'AR at just-identified fit')
result['aligned_tests']=report
with zipfile.ZipFile('/content/archive.zip','w',zipfile.ZIP_DEFLATED) as z:z.writestr('audit.json',json.dumps(result,indent=2,allow_nan=False))
print('archive_sha256',hashlib.sha256(Path('/content/archive.zip').read_bytes()).hexdigest())
