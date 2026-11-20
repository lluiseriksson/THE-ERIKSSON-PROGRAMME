"""Verify frozen table analyses and the analytic upper and lower certificates."""
from fractions import Fraction as F
from pathlib import Path
import json
import math
import subprocess
import sys

def check(ok,reason):
    if not ok:raise ValueError(reason)
root=Path(__file__).resolve().parent
def read(name):return json.loads((root/name).read_bytes())

for script,record in [('bgaa-cache.py','cache.json'),('bgaa-joint.py','joint.json'),('bgaa-activation.py','activation.json'),('bgaa-random.py','random.json')]:
    computed=json.loads(subprocess.check_output([sys.executable,str(root/script)],cwd=root))
    check(computed==read(record),record)
cert=read('random.json');rows=cert['stats']
model=read('joint.json')['Chronos-2']
for f,v in rows.items():
    check([F(v[k]) for k in ['slo','shi']]==[F(model['bands'][f]['warm_saving'][j]) for j in [0,2]],'independent savings')
    check(F(v['blo'])==F(read('activation.json')['Chronos-2']['sizes'][f]['min_setup']),'independent setup')
t=F(cert['inverse_e_upper']);rho=F(cert['rho']);h=F(cert['threshold_scale']);upper=F(cert['upper']);b0=F(cert['Bmin']);b1=F(cert['Bmax'])
check(t*sum(F(1,math.factorial(k)) for k in range(11))==1,'series')
check(h>0 and h<=b0<=b1,'bounds')
check(max(h*t+b1-h,rho*h*t+b1-b0)==upper,'uniform randomized bound')
x=cert['lower_witness'];B=F(x['setup']);S=F(x['saving']);k=B//S
check(S>0 and k>=1 and F(cert['lower'])==k*S*(1-S/B)**k,'fixed-size lower bound')
check(F(cert['lower'])<=upper<F(read('activation.json')['Chronos-2']['max_premium']),'strict improvement')
print('Reproduced four table analyses and verified the mixed-workload upper bound and constant-size lower witness.')
