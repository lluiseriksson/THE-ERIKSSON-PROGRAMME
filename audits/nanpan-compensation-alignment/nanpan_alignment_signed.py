import csv,json
from collections import defaultdict
from fractions import Fraction as F
govs=('Kunming','Yuxi','Honghe','Wenshan')
groups=defaultdict(dict)
with open('ring_spatial_incidence.csv',newline='') as f:
    for r in csv.DictReader(f):
        groups[r['calibration'],r['retention'],r['location']][r['kind'],r['unit']]=F(r['value'])
out=[]
for (cal,ret,loc),data in groups.items():
    b=[data['benefit_share_load',g] for g in govs]
    d=[-data['transfer_change_share_of_base_per_year',g] for g in govs]
    R=sum(d)
    if abs(R-data['transfer_change_share_of_base_per_year','Qujing'])>F(1,10**13):raise ValueError('Budget inconsistency')
    if not sum(b):
        if any(d):raise ValueError('Nonzero transfer in this no-benefit scenario')
        out.append(dict(calibration=cal,retention=ret,location=loc,status='undefined downstream benefit distribution'))
        continue
    s=[v/sum(b) for v in b]
    if min(s)<=0 or max(d)<=0:raise ValueError('Unsupported scenario')
    T=max(x/y for x,y in zip(d,s))
    boost=T-R
    z=[T*y-x for x,y in zip(d,s)]
    assert min(z)==0 and sum(z)==boost and all(x+v==T*y for x,v,y in zip(d,z,s))
    # After a uniform load surcharge the raw residual from proportionality is invariant.
    residual=[x-R*y for x,y in zip(d,s)]
    assert any(residual) and sum(residual)==0
    charged=[max(F(0),x+R*y) for x,y in zip(d,s)] if R>0 else []
    tv=sum(abs(v/sum(charged)-y) for v,y in zip(charged,s))/2 if charged else None
    out.append(dict(calibration=cal,retention=ret,location=loc,status='identified',signed_payers=[str(x) for x in d],benefit_shares=[str(y) for y in s],base_return=str(R),minimum=str(boost),minimum_float=float(boost),ratio_exact=str(boost/R) if R>0 else None,ratio=float(boost/R) if R>0 else None,bottleneck=[g for g,v in zip(govs,z) if v==0],surcharges_at_minimum=[str(v) for v in z],doubling_sufficient=boost<=R if R>0 else None,uniform_tv_at_doubling=float(tv) if tv is not None else None))
print(json.dumps(out,indent=2))