"""Check WLS recalibration directly against residualized-control weights."""
import hashlib, json, zipfile
from pathlib import Path
import numpy as np
g=[]; unit=[]; month=[]; weight=[]; treated=[]; sales=[]
for cohort in range(2):
    for firm in range(3+cohort):
        for t in range(5):
            g.append(cohort);unit.append((cohort,firm));month.append((cohort,t))
            weight.append((1+firm)/(1+cohort))
            treated.append(firm<1+cohort);sales.append((3*firm+1+t)**2+cohort)
post=np.array([i[1]>=2+i[0] for i in month])
tr=np.array(treated);d=(tr & post).astype(float);ctrl=(~tr)&post
x=np.array(sales);w=np.array(weight)
def indicators(rows):
    return np.array([[int(value==k) for k in sorted(set(rows))] for value in rows])
z=np.column_stack([indicators(unit),indicators(month)])
zmat=z*np.sqrt(w)[:,None]
res=d-z@np.linalg.lstsq(zmat,d*np.sqrt(w),rcond=None)[0]
h=w*res/np.dot(w,res*d)
q=-h[ctrl]
assert abs(q.sum()-1)<1e-12 and q.min()>0
def beta(f):
    y=np.log1p(np.where(ctrl,f*x,x))
    design=np.column_stack([d,z])*np.sqrt(w)[:,None]
    return np.linalg.lstsq(design,y*np.sqrt(w),rcond=None)[0][0]
cert=[]
for f1,f2 in [(1.,1.5),(.8,1.2),(1.2,1.)]:
    shift=beta(f2)-beta(f1)
    pred=-q@np.log((1+f2*x[ctrl])/(1+f1*x[ctrl]))
    assert abs(shift-pred)<1e-12
    assert abs(shift)<=abs(np.log(f2/f1))+1e-12
    assert np.sign(shift)==-np.sign(f2-f1)
    cert.append(dict(f1=f1,f2=f2,regression_shift=shift,formula_shift=pred))
# Fixed-effects residual identity does not require homogeneous cohort ratios.
total_abs=float(abs(q).sum())
out=dict(estimated_cases=cert,q_sum=float(q.sum()),q_min=float(q.min()),
    rows=len(x),positive_mass=(total_abs+1)/2,negative_mass=(total_abs-1)/2,
    max_discrepancy=max(abs(t['regression_shift']-t['formula_shift']) for t in cert),
    design='Two synthetic cohorts, complete rectangles, positive firm weights, cohort-month and firm-cohort fixed effects.')
with zipfile.ZipFile('/content/archive.zip','w',zipfile.ZIP_DEFLATED) as zf:zf.writestr('regression.json',json.dumps(out,indent=2))
print('archive_sha256',hashlib.sha256(Path('/content/archive.zip').read_bytes()).hexdigest())
