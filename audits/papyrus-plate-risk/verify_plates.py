"""Independent certificate using the active sets for the parity panel, with rational endpoints."""
from fractions import Fraction as F
from pathlib import Path
import json
v=json.loads(Path('bounds.json').read_bytes())
def require(ok):
    if not ok:raise ValueError('Certificate mismatch')
def root(k):
    a,b=F(0),F(1)
    for i in range(90):
        t=(a+b)/2
        if 20*t**k<1:a=t
        else:b=t
    return a,b
def risk(k,n):
    a,b=root(k)
    require(3*a>2)
    return (3*k*(1-b)/n,3*k*(1-a)/n)
def check(key,interval):
    r=v['results'][key];lo,hi=interval
    require(F(r['lower'])<=lo<=hi<=F(r['upper']))
check('integer_plate_floor',risk(24,110))
check('fold_floor',tuple((58*x+52*y)/110 for x,y in zip(risk(16,58),risk(8,52))))
require(v['odd_sizes']==[3]*16+[2]*5 and v['even_sizes']==[3]*8+[2]*14)
require(v['balanced_checks']==137 and F(97,100)**98>F(1,20)>F(97,100)**99)
print('Sharp plate and fold floors checked against the independent closed forms.')