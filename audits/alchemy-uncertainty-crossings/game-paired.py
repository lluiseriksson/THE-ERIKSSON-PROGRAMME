"""Sensitivity of fitted root contrasts and simultaneous whole-curve sign comparisons."""
import csv, hashlib, io, json, math, zipfile
from pathlib import Path
from statistics import NormalDist
from itertools import groupby
from operator import itemgetter

SRC='940203f567d74be15f38d1cfe97f7b2ea3ebfa9c68dcc1fb93884af381e8b41b'
NAMES=['S1_common_unique','S4_first_occurrences_unique_common','S4_repeated_rows_unique_common']
def load_models(source):
    if hashlib.sha256(source.read_bytes()).hexdigest()!=SRC:raise ValueError('Source edition mismatch')
    with zipfile.ZipFile(source) as z:
        def rows(name):
            key,=[n for n in z.namelist() if n.endswith('/outputs/decomposition/'+name+'.csv')]
            return list(csv.DictReader(io.StringIO(z.read(key).decode())))
        meta=rows('model_metadata');curves=rows('conditional_cbu_slope_curves')
    models=[]
    for name in NAMES:
        m,=[r for r in meta if r['model_id']==name]
        if m['progress_metric']!='unique_combination_progress':raise ValueError('Wrong scale')
        relevant=sorted([r for r in curves if r['model_id']==name],key=lambda r:float(r['progress']))
        u,s,a,h=[float(m[k]) for k in ('progress_reference_mean','progress_reference_sd','beta_cbu_at_reference','beta_cbu_x_progress')]
        # Recover the natural-progress polynomial about the first grid value by divided differences.
        def xy(r):return float(r['progress']),float(r['std_error'])**2
        (p0,v0),(p1,v1),(p2,v2)=map(xy,[relevant[0],relevant[len(relevant)//2],relevant[-1]])
        left=(v1-v0)/(p1-p0);right=(v2-v1)/(p2-p1);quad=(right-left)/(p2-p0)
        lin=left-quad*(p1-p0);a0=a+(p0-u)*h/s;slope=h/s
        if quad<=0 or v0*quad<(lin/2)**2:raise ValueError('Invalid covariance')
        def values(p):
            x=p-p0
            return a0+slope*x, math.sqrt(v0+x*(lin+quad*x))
        err=max(max(abs(values(float(r['progress']))[0]-float(r['estimate'])), abs(values(float(r['progress']))[1]/float(r['std_error'])-1)) for r in relevant)
        if err>1e-8:raise ValueError('Published grid mismatch')
        root=p0-a0/slope
        if abs(root-float(m['zero_crossing_progress']))>1e-6:raise ValueError('Root mismatch')
        se=values(root)[1]/abs(slope)
        models.append(dict(name=name,p0=p0,a=a0,h=slope,v=v0,c=lin/2,w=quad,root=root,se=se,grid_rows=len(relevant),residual=err,support=[int(m['progress_min']),int(m['progress_max'])],cbu_scale=[float(m[k]) for k in ('cbu_reference_mean','cbu_reference_sd')],singular=m.get('singular')))
    return models
def run(source):
    fits=load_models(source);first,second,repeat=fits
    if second['cbu_scale']!=repeat['cbu_scale']:raise ValueError('CBU scale differs')
    d=second['root']-first['root'];s1,s2=first['se'],second['se'];z=NormalDist().inv_cdf(.975)
    rho=(s1*s1+s2*s2-(d/z)**2)/(2*s1*s2)
    def delta_interval(r):
        v=(s1-s2)**2+2*s1*s2*(1-r)
        return [d-z*math.sqrt(v),d+z*math.sqrt(v)]
    if abs(delta_interval(rho)[0])>1e-10:raise ValueError('Boundary')
    # Two simultaneous Wald ellipses in dimension two. No cross-fit independence required.
    k=math.sqrt(-2*math.log(.05/2));lo=max(second['support'][0],repeat['support'][0]);hi=min(second['support'][1],repeat['support'][1])
    def band(m,p):
        x=p-m['p0'];mu=m['a']+x*m['h']
        width=k*math.sqrt(m['v']+2*x*m['c']+x*x*m['w'])
        return mu-width,mu+width
    def runs(pred):
        vals=[p for p in range(lo,hi+1) if pred(p)]
        out=[]
        for _,grp in groupby(enumerate(vals),lambda row:row[1]-row[0]):
            block=list(map(itemgetter(1),grp));out.append([block[0],block[-1]])
        return out
    regions=dict(first_positive_repeat_negative=runs(lambda p:band(second,p)[0]>0 and band(repeat,p)[1]<0),
                 repeat_negative=runs(lambda p:band(repeat,p)[1]<0),first_above_repeat=runs(lambda p:band(second,p)[0]>band(repeat,p)[1]),
                 repeat_above_first=runs(lambda p:band(repeat,p)[0]>band(second,p)[1]))
    return dict(fits=fits,root_difference=d,root_correlation_threshold=rho,delta_critical=z,delta_intervals={str(r):delta_interval(r) for r in (-1,0,.5,.9,1)},curve_critical=k,progress_domain=[lo,hi],regions=regions)
if __name__=='__main__':print(json.dumps(run(Path('source.zip')),sort_keys=True))
