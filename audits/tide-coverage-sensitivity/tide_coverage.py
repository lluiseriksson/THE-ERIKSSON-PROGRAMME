"""Recompute the fixed NOAA panel. Run next to the downloaded JSON files."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
from math import sqrt
from collections import Counter
from datetime import datetime
import calendar,hashlib,json
STATIONS=('8443970','8724580','8771450','9414290','9447130','1612340')
def require(test,reason):
    if not test:raise ValueError(reason)
def read(p):return json.loads(Path(p).read_bytes())
def signed_square(y,f,c):
    require(y>0 and f>0,'Nonpositive variance')
    return c*abs(c)/(y*f)
def mix(a,b,t):return tuple(x+(z-x)*t for x,z in zip(a,b))
def extremes(stats,lam):
    """Physical moments Y variance, F variance, covariance, common station mask."""
    n=len(stats);base=tuple(sum(col)/n for col in zip(*stats));v=[mix(x,base,lam) for x in stats]
    cand=[]
    def add(i,j,t):
        score=signed_square(*mix(v[i],v[j],t));w=[lam/n]*n
        w[i]+=(1-lam)*(1-t);w[j]+=(1-lam)*t
        require(sum(w)==1 and min(w)>=lam/n,'Infeasible witness')
        raw=tuple(sum(wi*xi for wi,xi in zip(w,col)) for col in zip(*stats))
        require(signed_square(*raw)==score,'Wrong reconstructed witness')
        cand.append((score,tuple(w)))
    for i in range(n):add(i,i,Q(0))
    for i,j in combinations(range(n),2):
        y,f,c=v[i];Y,F,C=v[j]
        dy,df,dc=Y-y,F-f,C-c
        # Derivative of covariance divided by geometric mean of variances.
        g0=2*dc*y*f-c*(dy*f+y*df)
        g1=dc*(dy*f+y*df)-2*c*dy*df
        if g1 and 0<-g0/g1<1:add(i,j,-g0/g1)
    lo,hi=min(cand),max(cand)
    # Independent candidate construction in projective coordinates.
    pts=[(f/y,c/y) for y,f,c in v]
    scores=[b*abs(b)/a for a,b in pts]
    for (a,b),(x,z) in combinations(pts,2):
        if x==a or z==b:continue
        slope=(z-b)/(x-a);inter=b-slope*a;root=inter/slope
        if min(a,x)<root<max(a,x):
            val=slope*root+inter;scores.append(val*abs(val)/root)
    require([lo[0],hi[0]]==[min(scores),max(scores)],'Methods disagree')
    return lo,hi
def record(candidate):
    v,w=candidate
    return dict(signed_r2=str(v),correlation=(1 if v>=0 else -1)*sqrt(abs(v)),weights=[str(x) for x in w])
def threshold(stats,target):
    def ok(n):return extremes(stats,Q(n,10000))[0][0]>=target**2
    if ok(0):return dict(status='already',first=0)
    if not ok(10000):return dict(status='unattainable')
    low,high=0,10000
    while high-low>1:
        mid=(low+high)//2
        if ok(mid):high=mid
        else:low=mid
    return dict(status='bracketed',last_failing=low,first_passing=high,denominator=10000)
def amounts(p,kind):
    doc=read(p)
    if 'error' in doc:
        require('No data was found' in doc['error']['message'],'Unknown response')
        return {},doc['error']['message']
    result={}
    for x in doc[kind]:
        t=x['t'];dt=datetime.strptime(t,'%Y-%m-%d %H:%M');require(dt.minute==0 and t not in result and dt.year==2024 and dt.month in [1,2],t)
        val=x.get('v','').strip();unflagged=all(f.strip()=='0' for f in x.get('f','0').split(','))
        result[t]=Q(val) if val and unflagged else None
    return result,None
def month_data(month,manifest):
    rows={};stats=[]
    for st in STATIONS:
        y,e1=amounts(st+'-hourly_height.json','data');f,e2=amounts(st+'-predictions.json','predictions')
        prefix=f'2024-{month:02d}';num=calendar.monthrange(2024,month)[1]*24
        keys=sorted(t for t in y.keys()&f.keys() if t.startswith(prefix) and y[t]!=None and f[t]!=None)
        n=len(keys);details=rows[st]=dict(matched=n,calendar_hours=num,excluded_or_missing=num-n,flagged_or_blank_obs=sum(t.startswith(prefix) and val is None for t,val in y.items()))
        if 10*n<9*num:details.update(excluded=e1 or e2 or 'Below 90%');continue
        pairs=[(y[t],f[t]) for t in keys]
        def avg(values):return sum(values)/n
        my,mf=map(avg,zip(*pairs))
        centered=[(a-my,z-mf) for a,z in pairs]
        sy=avg(a*a for a,z in centered);sf=avg(z*z for a,z in centered)
        dep=avg((z-a)**2 for a,z in centered);cov=avg(a*z for a,z in centered)
        require((sy+sf-dep)/2==cov,'Departure/mask mismatch')
        if not sy or not sf:details.update(excluded='Zero variance');continue
        stats.append((sy,sf,cov));details.update(moments=list(map(str,stats[-1])),local=record((signed_square(sy,sf,cov),[Q(1)]))['correlation'])
    require(len(stats)>=2,'Too few stations')
    envelope={}
    for lam in [Q(0),Q(1,2),Q(1)]:
        envelope[str(lam)]=list(map(record,extremes(stats,lam)))
    return dict(stations=rows,weight_order=[s for s in STATIONS if 'moments' in rows[s]],envelope=envelope,thresholds={str(t):threshold(stats,t) for t in [Q(9,10),Q(19,20)]})
def main():
    man=read('noaa-manifest.json')
    for name,entry in man.items():require(hashlib.sha256(Path(name).read_bytes()).hexdigest()==entry['sha256'],'Input hash mismatch')
    t=[tuple(map(Q,row)) for row in [(1,1,1),(4,16,8)]]
    lo,hi=extremes(t,Q(0));require((lo[0],hi[0])==(Q(8,9),1) and lo[1]==(Q(8,9),Q(1,9)),'Interior witness')
    print(json.dumps(dict(months={str(m):month_data(m,man) for m in [1,2]},interior_check=record(lo)),sort_keys=True,indent=2))
if __name__=='__main__':main()