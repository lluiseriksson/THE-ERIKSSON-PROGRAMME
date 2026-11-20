"""Reconstruct group coefficients directly from two independent basis panels."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
def read(f):return json.loads(Path(f).read_bytes())
def check(ok,msg):
    if not ok:raise ValueError(msg)
r=read('retention.json');pairs=read('thinning.json');counts={}
for k in range(1,7):
    for sel in combinations(range(6),k):
        shape=''.join(str(v) for v in sorted([sum(i//2==j for i in sel) for j in range(3)],reverse=True))
        counts.setdefault(shape,[]).append(sel)
check(set(counts)==set(r['patterns']),'shape coverage')
for shape,events in counts.items():
    got=[]
    for panel,variance in [([1,1,-1,-1,0,0],F(2,3)),([1,-1,1,-1,1,-1],F(1))]:
        got.append(sum(F(sum(panel[i] for i in ev),len(ev))**2 for ev in events)/len(events)/variance)
    check(got==list(map(F,r['patterns'][shape])),shape)
cap=max(max(map(F,r['patterns'][s])) for s in counts if sum(map(int,s))>=3)
check(cap==F(1,3),'adaptive cap')
minimum={}
for m,data in r['models'].items():
    e,b,w=map(F,pairs['effects'][m]);d=F(data['C3_dispersion'])
    for shape,ci in data['fixed'].items():
        x,y=map(F,r['patterns'][shape])
        center=e+x*b+y*w;radius=F(1,200000)+(x+y)*F(1,20000)
        check([center-radius,center+radius]==list(map(F,ci)),'shape enclosure')
    upper=e+F(1,200000)+cap*(d+F(1,20000))
    check(upper==F(data['adaptive_vs_full_upper']) and upper<0,'adaptive comparison')
    if e+F(1,200000)+d+F(1,20000)<0:
        minimum[m]=1
    else:
        check(F(data['fixed']['200'][0])>0,'two-output counterexample')
        minimum[m]=3
check(r['identity_checks']==len(counts)*3**6*2,'enumeration count')
print(json.dumps(minimum,sort_keys=True))