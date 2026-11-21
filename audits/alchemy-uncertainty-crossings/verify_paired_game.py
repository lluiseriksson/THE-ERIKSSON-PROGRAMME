"""Offline cross-check of the stated endpoints and the digest-linked coverage record."""
from pathlib import Path
from statistics import NormalDist
import json,math

def need(ok,why):
    if not ok: raise ValueError(why)

def run():
    stats=json.loads(Path('paired-crossings.json').read_bytes());cover=json.loads(Path('coverage.json').read_bytes())
    a,b,r=stats['fits'];d=b['root']-a['root']
    z=NormalDist().inv_cdf(.975);rho=stats['root_correlation_threshold']
    need(abs(d-z*math.sqrt(a['se']**2+b['se']**2-2*rho*a['se']*b['se']))<1e-7,'Root comparison')
    k=stats['curve_critical']
    def neighbors(m,p):
        x=p-m['p0'];est=m['a']+x*m['h'];var=m['v']+2*m['c']*x+m['w']*x*x
        return est-k*math.sqrt(var),est+k*math.sqrt(var)
    spans={key:[] for key in ['first_positive_repeat_negative','first_above_repeat','repeat_negative','repeat_above_first']}
    for p in range(stats['progress_domain'][0],stats['progress_domain'][1]+1):
        L,U=neighbors(b,p);l,u=neighbors(r,p)
        for key,yes in zip(spans,(L>0>u,L>u,u<0,l>U)):
            if yes:
                if spans[key] and spans[key][-1][-1]==p-1:spans[key][-1][1]=p
                else:spans[key].append([p,p])
    need(spans==stats['regions'],'Band regions')
    spec=json.loads(Path('spec.json').read_bytes());need(spec['source']['sha256']==cover['source_sha256'] and spec['regions']==cover['regions'],'Empirical run identity')
    frame=cover['coverage']['first_positive_repeat_negative']
    need(cover['totals']==[6212596,4691033,1521563,29493] and all(frame[k]['rows_total']>=frame[k]['covered_rows'] for k in ('first','repeat')),'Source coverage')
    return dict(rho=round(rho,9),regions=spans,observed_rows=[frame[k]['covered_rows'] for k in ('first','repeat')])
base_result=run()
from statistics import NormalDist
from math import sqrt
p=json.loads(Path('player-pair.json').read_bytes());v=p['covariance'];d=p['shift'];z=NormalDist().inv_cdf(.975);se=sqrt(v[0][0]+v[1][1]-2*v[0][1]);need(abs(se-p['se'])<1e-8 and abs(d-z*se-p['interval'][0])<1e-7 and abs(d+z*se-p['interval'][1])<1e-7,'Paired variance')
print(json.dumps({**base_result,'paired_se':round(se,6),'players':p['players']},sort_keys=True))
