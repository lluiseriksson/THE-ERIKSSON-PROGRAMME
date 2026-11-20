"""Sensitivity of the reported stock-level CAR comparison to a common set of weights."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,zipfile,io,os
from urllib.request import urlopen
from scipy.optimize import linprog
SRC='https://zenodo.org/api/records/24405076/files/Metering_Gap_replication_v1.0.zip/content'
PIN='eac22121ea0ddb2a5d3af94a48f2d1b031424ab6377fa86d0a6c87f51243d11d'
path=Path('deposit.zip')
data=path.read_bytes() if path.is_file() else urlopen(SRC,timeout=30).read()
if hashlib.sha256(data).hexdigest()!=PIN:raise ValueError('Source package digest')
with zipfile.ZipFile(io.BytesIO(data)) as z:
    entry,=[n for n in z.namelist() if n.replace(chr(92),'/')=='Metering_Gap_replication_v1.0/analisis/event_study_resultados.json']
    rows=json.loads(z.read(entry),parse_float=F)
def dot(a,b):return sum(x*y for x,y in zip(a,b,strict=True))
def tv(w):return sum(abs(x-F(1,len(w))) for x in w)/2
def boundary(gap):
    n=len(gap);w=[F(1,n)]*n;loss=dot(w,gap);target=min(range(n),key=gap.__getitem__)
    if loss<=0:return w
    for i in sorted(range(n),key=gap.__getitem__,reverse=True):
        slope=gap[i]-gap[target]
        if slope<=0:break
        change=min(w[i],loss/slope)
        w[i]-=change;w[target]+=change;loss-=slope*change
        if not loss:
            if dot(w,gap)!=0 or min(w)<0 or sum(w)!=1:raise ValueError('Bad certificate')
            return w
    return None
def lp(gap):
    n=len(gap);identity=[[int(i==j) for i in range(n)] for j in range(n)]
    # z bounds only positive deviations; their sum is total variation on a simplex.
    inequalities=[list(map(float,gap))+[0]*n]+[r+[-v for v in r] for r in identity]
    a=linprog([0]*n+[1]*n,A_ub=inequalities,b_ub=[0]+[1/n]*n,A_eq=[[1]*n+[0]*n],b_eq=[1],bounds=(0,None),method='highs')
    if a.status==2:return None
    if not a.success:raise RuntimeError(a.message)
    return a.fun
def min_box(gap,lo,hi):
    n=len(gap);w=[lo]*n;remaining=1-n*lo
    for i in sorted(range(n),key=gap.__getitem__):
        z=min(remaining,hi-lo);w[i]+=z;remaining-=z
    if remaining:raise ValueError('Empty box')
    return w
out={}
for factor in [False,True]:
    a,b=[next(r for r in rows if r['event']==e and r['factor2']==factor) for e in ('B1','B4')]
    names=list(a['stocks']);n=len(names);u=[F(1,n)]*n
    if set(names)!=set(b['stocks']) or n!=8:raise ValueError('Issuer support')
    initial=[a['stocks'][k] for k in names];final=[b['stocks'][k] for k in names]
    series=[initial,final];reported=[a['[-1,+1]']['CAR%'],b['[-1,+1]']['CAR%']]
    if any(abs(dot(x,u)-y)>F(1,100) for x,y in zip(series,reported)):raise ValueError('Portfolio reconciliation')
    result=dict(issuers=names,initial=initial,final=final,equal=[dot(u,x) for x in series],reported=reported,boundaries={})
    for tag,sgn in [('difference',-1),('sum',1)]:
        g=[x+sgn*y for x,y in zip(*series)]
        rec={}
        for offset in [F(-1,100),F(0),F(1,100)]:
            coeff=[x+offset for x in g];ext=boundary(coeff);other=lp(coeff)
            if ext is None:
                if other is not None:raise ValueError('Infeasibility disagreement')
            elif other is None or abs(float(tv(ext))-other)>1e-9:raise ValueError('LP disagreement')
            rec[str(offset)]=None if ext is None else dict(radius=tv(ext),w=ext,event_car=[dot(x,ext) for x in series])
        w=min_box(g,F(1,20),F(1,5));rec['box']=dict(w=w,value=dot(w,g),event_car=[dot(x,w) for x in series])
        result['boundaries'][tag]=rec
    out['market_smh' if factor else 'market']=result
# A common weight vector across both alternative factor specifications.
joint={}
for off in [F(-1,100),F(0),F(1,100)]:
    specs={}
    for key,z in out.items():
        a,b=z['initial'],z['final'];n=len(a);u=[F(1,n)]*n
        g=[x-y+off for x,y in zip(a,b)]
        order=sorted(range(n),key=g.__getitem__);half=n//2
        direction=[1 if i in order[:half] else -1 for i in range(n)]
        rmax=dot(u,g)/(-dot(g,direction))
        if not (0<rmax<F(1,n)):raise ValueError('Simplex clipping requires another segment')
        w=[x+rmax*t for x,t in zip(u,direction)]
        if dot(g,w)!=0:raise ValueError('Max-norm boundary mismatch')
        # Exclude the other absolute-value branch even in the largest box used here.
        sumg=[x+y+off for x,y in zip(a,b)]
        if dot(min_box(sumg,F(0),F(2,n)),sumg)<=0:raise ValueError('Sum boundary in box')
        tvrec=z['boundaries']['difference'][str(off)]
        if not tvrec['radius']<z['boundaries']['sum'][str(off)]['radius']:raise ValueError('Other TV branch is closer')
        specs[key]=dict(tv=tvrec['radius'],tv_w=tvrec['w'],maxnorm=rmax,maxnorm_w=w)
    joint[str(off)]={}
    for norm in ['tv','maxnorm']:
        key=max(specs,key=lambda k:specs[k][norm]);w=specs[key][norm+'_w']
        evals={k:[dot(z['initial'],w),dot(z['final'],w)] for k,z in out.items()}
        if not all(a-b+off<=0 and a+b>abs(off) for a,b in evals.values()):raise ValueError(('joint witness',norm,evals))
        joint[str(off)][norm]=dict(radius=specs[key][norm],weights=w,events=evals,binding=key,individual={k:d[norm] for k,d in specs.items()})
stress={}
# A whole-percentage allocation with every issuer present and both corrected gaps negative.
for a in range(13,26):
    z=out['market_smh'];g=[x-y for x,y in zip(z['initial'],z['final'])]
    if a>25:break
    w=min_box(g,F(25-a,100),F(a,100))
    scores={k:[dot(s['initial'],w),dot(s['final'],w)] for k,s in out.items()}
    if all(b-a>F(1,100) and a>0 for a,b in scores.values()):
        stress=dict(weights=w,events=scores);break
if not stress:raise ValueError('No strictly reversing test portfolio')
print(json.dumps(dict(specs=out,joint=joint,strict_counterexample=stress),default=str))