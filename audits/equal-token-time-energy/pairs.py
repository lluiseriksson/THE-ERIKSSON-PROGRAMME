"""Compare pairs of grid workloads using fixed token totals and published regressions."""
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, product
from collections import defaultdict
from pathlib import Path
from urllib.request import urlopen
import json,re,zipfile

url='https://arxiv.org/html/2610.39621v2'
with urlopen(url,timeout=40) as response:
    raw=response.read()
s=raw.decode()
table=s.split('id="S4.T2"')[1].split('</table>')[0]
rows=re.findall(r'<tr.*?</tr>',table,re.S)
def parameter(c):
    v,=re.findall('alttext="([^"]*)"',c)
    part=v.split(r'\times 10^')
    scale=Q(10)**int(part[1].strip('{}')) if len(part)>1 else Q(1)
    places=len(part[0].split('.')[1]) if '.' in part[0] else 0
    return scale*Q(part[0]),scale/(2*10**places)
coef=[]
for i,row in enumerate(rows[2:]):
    c=re.findall(r'<t[dh]\b.*?</t[dh]>',row,re.S)
    assert '\\beta_{'+str(i)+'}' in c[0] and len(c)==4
    coef.append(list(map(parameter,c[1:])))
assert len(coef)==5 and coef[2][0][0]==Q('2.70e-7')
grid=list(product(range(10000,200001,10000),range(500,2001,500)))
def moments(pair):
    return tuple(map(sum,zip(*((1,i,i*i,o,i*o) for i,o in pair))))
by_total=defaultdict(list)
for pair in combinations_with_replacement(grid,2):
    v=moments(pair)
    by_total[v[1],v[3]].append((pair,v))
def delta(u,v):
    ds=[b-a for a,b in zip(u,v)]
    assert ds[0]==ds[1]==ds[3]==0
    return [(sum(ds[k]*coef[k][j][0] for k in (2,4)),sum(abs(ds[k])*coef[k][j][1] for k in (2,4))) for j in range(3)]
pairs=count=robust=0
best=None
for group in by_total.values():
    for (a,u),(b,v) in combinations(group,2):
        pairs+=1
        (t,dt),(local,dl),(e,de)=delta(u,v)
        if t*e>=0:continue
        count+=1
        if abs(t)<=dt or abs(e)<=de:continue
        robust+=1
        if t<0:a,b=b,a;t,local,e=-t,-local,-e
        if best is None or -e-de>best[0]:
            best=(-e-de,dict(a=a,b=b,api_ms=str(t),local_ms=str(local),energy_Wh=str(e),energy_radius_Wh=str(de),time_radius_ms=str(dt)))
a=((40000,500),(40000,1500));b=((10000,1500),(70000,500))
w=delta(moments(a),moments(b))
assert [v for v,_ in w]==[Q(117),Q(-594),Q('-0.07824')]
assert all(abs(v)>err for v,err in w)
r=dict(source=url,html_sha256=sha256(raw).hexdigest(),table_sha256=sha256(table.encode()).hexdigest(),grid_points=len(grid),portfolios=sum(map(len,by_total.values())),comparable_unordered_pairs=pairs,nominal_reversals=count,rounding_robust=robust,maximum_guaranteed_energy_decrease=best[1],simple_example=dict(a=a,b=b,estimates_and_radii=[[str(t),str(d)] for t,d in w]))
dest=Path('/content/archive.zip')
with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('pairs.json',json.dumps(r,indent=2))
print('archive_sha256',sha256(dest.read_bytes()).hexdigest())
