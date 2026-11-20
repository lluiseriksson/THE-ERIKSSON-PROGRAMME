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
assert sha256(table.encode()).hexdigest()=='6917432e83d17e399a68d223a2c267d2daad671456b212f019df3b6027dda5fb'
from collections import Counter
from itertools import product
def full(v,j):return sum(x*coef[k][j][0] for k,x in enumerate(v))
def frontier(points):
    keep=[];energy=Q(-1)
    for t,e in sorted(points,reverse=True):
        if e>energy:
            keep.append((t,e));energy=e
    assert all(t1>t2 and e1<e2 for (t1,e1),(t2,e2) in zip(keep,keep[1:]))
    assert all(any(T>=t and E>=e for T,E in keep) for t,e in points)
    return keep
cloud={};best=(-1,None);count=0
for group in by_total.values():
    for (a,u),(b,v) in combinations(group,2):
        (t,rt),_,(e,re_)=delta(u,v)
        if t*e>=0 or abs(t)<=rt or abs(e)<=re_:continue
        if t<0:a,b=b,a;u,v=v,u;t,e=-t,-e
        count+=1
        assert not set(a)&set(b)
        tlo=t-rt;elo=-e-re_
        corners=(tlo/4,elo/4)
        record={'a':a,'b':b,'time_ms':str(t),'energy_Wh':str(e)}
        cloud.setdefault(corners,record)
        dt=full(u,0)+full(v,0);de=full(u,2)+full(v,2)
        assert dt>0 and de>0
        relative=min(tlo/dt,elo/de)
        if relative>best[0]:best=(relative,dict(record,relative_time=str(tlo/dt),relative_energy=str(elo/de)))
f=frontier(cloud)
# Direct check on the non-dominated witnesses: evaluate the published predictions
# at each cell and all 4 relevant coefficient vertices separately for each outcome.
for t,e in f:
    a,b=map(cloud[t,e].get,['a','b'])
    cnt=Counter(b);cnt.subtract(a)
    for j,expected,orient in [(0,4*t,1),(2,4*e,-1)]:
        values=[]
        for u,v in product((-1,1),repeat=2):
            def fit(point):
                i,o=point
                terms=(1,i,i*i,o,i*o)
                return sum(terms[k]*(coef[k][j][0]+{2:u,4:v}.get(k,0)*coef[k][j][1]) for k in range(5))
            values.append(orient*sum(m*fit(cell) for cell,m in cnt.items()))
        assert min(values)==expected and sum(map(abs,cnt.values()))==4
assert count==2574
result=dict(source=url,table_sha256=sha256(table.encode()).hexdigest(),robust_pairs=count,
    frontier=[dict(time_error_ms=str(t),energy_error_Wh=str(e),**cloud[t,e]) for t,e in f],
    best_common_relative_fraction=str(best[0]),relative_witness=best[1])
dest=Path('/content/archive.zip')
with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('frontier.json',json.dumps(result,indent=2))
print('archive_sha256',sha256(dest.read_bytes()).hexdigest())
