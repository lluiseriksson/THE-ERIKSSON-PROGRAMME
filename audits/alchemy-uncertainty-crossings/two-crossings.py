"""Invert the published Wald tests for the zero of the conditional CBU slope."""
from pathlib import Path
from statistics import NormalDist
import csv,io,json,math,zipfile,hashlib
def run(p):
    if hashlib.sha256(p.read_bytes()).hexdigest()!='940203f567d74be15f38d1cfe97f7b2ea3ebfa9c68dcc1fb93884af381e8b41b':raise ValueError('Source hash')
    with zipfile.ZipFile(p) as z:
        def rows(name):
            key,=[n for n in z.namelist() if n.endswith('/outputs/decomposition/'+name+'.csv')]
            return list(csv.DictReader(io.StringIO(z.read(key).decode('utf8'))))
        metadata=rows('model_metadata');curves=rows('conditional_cbu_slope_curves')
    ids=['S1_common_unique','S4_first_occurrences_unique_common']
    crit=NormalDist().inv_cdf(1-.05/(2*len(ids)))
    ans={}
    for k in ids:
        meta,=[r for r in metadata if r['model_id']==k]
        lines=sorted([r for r in curves if r['model_id']==k],key=lambda r:float(r['progress']))
        u=float(meta['progress_reference_mean']);s=float(meta['progress_reference_sd'])
        a=float(meta['beta_cbu_at_reference']);h=float(meta['beta_cbu_x_progress'])
        def moments(row):return (float(row['progress'])-u)/s,float(row['std_error'])**2
        (x0,v0),(x1,v1),(x2,v2)=map(moments,[lines[0],lines[len(lines)//2],lines[-1]])
        d01=(v1-v0)/(x1-x0);d12=(v2-v1)/(x2-x1)
        vv=(d12-d01)/(x2-x0);twocov=d01-vv*(x1+x0);va=v0-x0*twocov-x0*x0*vv
        if min(va,vv)<=0 or va*vv<=(twocov/2)**2:raise ValueError('Covariance')
        errors=[]
        for row in lines:
            x,v=moments(row);errors.append(abs((va+x*twocov+x*x*vv)/v-1))
            if abs(a+x*h-float(row['estimate']))>1e-8:raise ValueError('Slope')
        if max(errors)>1e-8:raise ValueError('Variance reconstruction')
        A=h*h-crit*crit*vv;B=2*a*h-crit*crit*twocov;C=a*a-crit*crit*va
        disc=B*B-4*A*C
        if A<=0 or disc<=0:raise ValueError('Unbounded or disjoint Fieller set')
        l,r=sorted(u+s*(-B+sign*math.sqrt(disc))/(2*A) for sign in [-1,1])
        point=u-s*a/h
        if not (float(meta['progress_min'])<=l<point<r<=float(meta['progress_max'])):raise ValueError('Support')
        ans[k]=dict(point=point,interval=[l,r],relative_variance_residual=max(errors),tested_rows=len(lines))
    first,second=[ans[k]['interval'] for k in ids]
    return dict(coverage='Nominal asymptotic 95% simultaneous for the two true zeros under the reported marginal Wald models, by Bonferroni; cross-fit covariance unspecified.',critical=crit,models=ans,difference_outer=[second[0]-first[1],second[1]-first[0]])
if __name__=='__main__':print(json.dumps(run(Path('source.zip')),sort_keys=True))
