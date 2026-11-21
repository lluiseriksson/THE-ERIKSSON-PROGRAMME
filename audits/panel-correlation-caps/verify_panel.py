import json,runpy
from pathlib import Path
from fractions import Fraction as F
v=runpy.run_path('panel-power.py')['main']()
if v!=json.loads(Path('panel-bounds.json').read_bytes()):raise ValueError('Certificate mismatch')
k,l=7,27;x=[F(l,k+l)]*k+[-F(k,k+l)]*l
for row in [v['exact'],*v['rounding_corners']]:
    h1,h0,hc=map(F,row['worst_correlations']);mean=F(row['mean_factor']);S=(k+l)*(mean-1)
    if k*(k-1)*h1+l*(l-1)*h0+2*k*l*hc!=S:raise ValueError('Correlation mass')
    if hc!=0 or not (0<=h0<=h1<=1):raise ValueError('Non-PSD block witness')
    def entry(i,j):
        if i==j:return 1
        if i<k and j<k:return h1
        return h0 if i>=k and j>=k else hc
    ray=sum(x[a]*entry(a,b)*x[b] for a in range(34) for b in range(34))/sum(z*z for z in x)
    if ray!=1+(k*(k-1)*h1*F(l,k)+l*(l-1)*h0*F(k,l))/34:raise ValueError('Matrix differs')
    if row['cap_half'][1]>=250000 or row['cap_seven_tenths'][0]<=250000:raise ValueError('Sensitivity does not separate')
print(json.dumps(v['exact'],sort_keys=True))
