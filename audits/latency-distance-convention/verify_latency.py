"""Offline exact reconstruction of central scores, rounding extrema and mass transfer."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

def read(name):
    return json.loads(Path(name).read_bytes())

src=read("fuente.json"); checked=read("replay.json")['results'];grid=read("rms.json")
xy=list(product(src['grid']['input'],src['grid']['output']))
c=[F(l)-F(a) for a,l in zip(src['api'],src['local'])]
e=[F(l)+F(a) for a,l in zip(src['api_halfwidth'],src['local_halfwidth'])]
def predict(b,cell):
    i,o=cell
    return b[0]*i+b[1]*i*i+b[2]*o+b[3]*i*o
def mean(v):return sum(v)/len(v)
errors=[predict(c,x) for x in xy];nom=mean([v*v for v in errors]);with_offset=mean([(v+F('217.03'))**2 for v in errors])
if nom!=F(grid['central_squared']) or not (F('1869.5')**2<with_offset<F('1870.5')**2):raise ValueError('Central scores')
for key in ['min_squared','max_squared']:
    if grid[key]!=checked['zero_intercepts'][key]:raise ValueError('Rounding crosscheck')
if F(grid['min_squared'])<=F('1870.5')**2:raise ValueError('Rounding not separated')
w=checked['weights'];masses={cell:F(1,80) for cell in xy};recipient=tuple(w['recipient'])
for source,amount in w['uniform_mass_donors']:
    masses[tuple(source)]-=F(amount);masses[recipient]+=F(amount)
if min(masses.values())<0 or sum(masses.values())!=1 or sum(weight*predict(c,cell)**2 for cell,weight in masses.items())!=1870**2:raise ValueError('Redistribution witness')
print('Exact mean squared errors and transfer of workload mass verified.')
