"""Compare tabulated curves at a common inflow. Run on Linux with numpy."""
import argparse, csv, hashlib, io, itertools, json
from pathlib import Path
from urllib.request import urlopen
import numpy as np

root='https://raw.githubusercontent.com/NatLabRockies/SAM/784177b634fa1475fda6672b70595e087a238aea/deploy/'
def fetch(url,digest):
    with urlopen(url,timeout=45) as response: raw=response.read()
    if hashlib.sha256(raw).hexdigest()!=digest: raise ValueError('source hash mismatch')
    return raw
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('site', choices=['north-dakota','minnesota'])
parser.add_argument('output', type=Path)
args = parser.parse_args()
sites = {
    'north-dakota': ('ND%20Northern-Flat%20Lands.srw','60c816a70089a5d20e4a50cd380f74b5e701630babb4e73132a5ccb829b57819'),
    'minnesota': ('MN%20Southwestern-Flat%20Lands.srw','d5c0cefc5942f6c3a5d83986d6410d9b37b56d4be0cc2d078b66bd69b0382ce0')
}
resource_file,resource_sha=sites[args.site]
resource=fetch(root+'wind_resource/'+resource_file,resource_sha)
library=fetch(root+'libraries/Wind%20Turbines.csv','dcfbf9149a82dce3eaa1de07002ede19c73e4eea31456109eceacaf27fc0b2c1')
def table(raw):return list(csv.reader(io.StringIO(raw.decode('utf-8-sig',errors='strict'))))
rows=table(resource)
col=next(i for i,(k,h,u) in enumerate(zip(rows[2],rows[4],rows[3])) if (k,h,u)==('Speed','80','m/s'))
v=np.array([float(r[col]) for r in rows[5:] if r])
if len(v)!=8760 or not np.all(np.isfinite(v)&(v>=0)):raise ValueError('invalid wind series')
reps=np.array([2.99,3.18,6.25,10.12])
groups=np.abs(v[:,None]-reps).argmin(axis=1)
bins=[v[groups==i] for i in range(len(reps))]
means=np.array([np.mean(x) for x in bins])
weights=np.array([len(x)/len(v) for x in bins])
curves={}
skipped=[]
for row in table(library)[3:]:
    if len(row)<6 or not row[1]:continue
    r=float(row[1].strip().removesuffix('kW').strip())
    if not 1000<=r<=5000:continue
    name=row[0].strip()
    if args.site=='minnesota' and name not in ('Fuhrlander FL 1500_70','GE 1.5sle'):continue
    x,y=[np.fromstring(a,sep='|') for a in row[4:6]]
    if len(x)!=len(y) or len(x)<2 or not np.all(np.diff(x)>0) or not np.isfinite(y).all() or not np.isfinite(x).all() or min(y)<0 or (x[0]>min(v) and y[0]!=0) or (x[-1]<max(v) and y[-1]!=0) or name in curves:
        skipped.append(name)
        continue
    curves[name]=(r,x,y)
def power(curve,s):return np.interp(s,curve[1],curve[2],left=0,right=0)
stats={name:[float(power(curve,v).mean()),float(weights@power(curve,means))] for name,curve in curves.items()}
comparison=[];eligible=0
for a,b in itertools.combinations(curves,2):
    if curves[a][0]!=curves[b][0]:continue
    eligible+=1
    exact,approx=np.subtract(stats[a],stats[b])
    if exact*approx<0 and min(abs(exact),abs(approx))>1e-7:
        comparison.append(dict(a=a,b=b,rating=curves[a][0],hourly_kw=float(exact),four_mean_kw=float(approx)))
comparison.sort(key=lambda p:-min(abs(p['hourly_kw']),abs(p['four_mean_kw']))/p['rating'])
report=dict(source=root,hours=len(v),height_m=80,assignment='nearest of four fixed speeds, first on tie; evaluate at realized bin means',groups=[dict(n=len(a),mean=float(a.mean()),lo=float(a.min()),hi=float(a.max())) for a in bins],range_kw=[1000,5000],number_curves=len(curves),eligible_pairs=eligible,excluded_curves=skipped,reversals=comparison,means_by_curve=stats)
if comparison:
    win=comparison[0];a,b=[curves[win[k]] for k in ('a','b')]
    # Sharp per-bin bounds with continuous speeds, mean and support. Linear interpolation between tabulated knots.
    def diff(t):return power(a,t)-power(b,t)
    bounds=[]
    for u,m in zip(bins,means):
        lo,hi=float(min(u)),float(max(u))
        grid=np.unique(np.clip(np.r_[lo,hi,m,a[1],b[1]],lo,hi))
        vals=[float(diff(m))]
        for l in grid[grid<m]:
            for h in grid[grid>m]:
                vals.append(float(((h-m)*diff(l)+(m-l)*diff(h))/(h-l)))
        bounds.append([min(vals),max(vals)])
    aggregate=weights@np.array(bounds)
    if not aggregate[0]-1e-7<=win['hourly_kw']<=aggregate[1]+1e-7:raise ValueError('hourly gap outside envelope')
    report['envelope_kw']=[float(z) for z in aggregate]
    report['per_bin_envelope_kw']=bounds
    # Second implementation from the empirical positive-part moments and jumps of slopes.
    grid=np.unique(np.r_[min(v),max(v),a[1],b[1]])
    grid=grid[(grid>=min(v))&(grid<=max(v))]
    values=diff(grid)
    s=np.diff(values)/np.diff(grid)
    gap=float(values[0]+s[0]*(v.mean()-grid[0])+sum(jump*np.maximum(v-knot,0).mean() for knot,jump in zip(grid[1:-1],np.diff(s))))
    if abs(gap-win['hourly_kw'])>1e-7:raise ValueError('independent sum disagrees')
    report['hinge_reconstruction_kw']=gap
with args.output.open('x',encoding='utf-8') as stream:
    json.dump(report,stream,indent=2,allow_nan=False)
