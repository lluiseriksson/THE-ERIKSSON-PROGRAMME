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
from scipy.optimize import linprog
# Time in 10 s units and energies in Wh keep the LP well scaled.
def fit(cell,j):
    i,o=cell
    return sum(x*coef[k][j][0] for k,x in enumerate((1,i,i*i,o,i*o)))
data=[(Q(i,100000),Q(o,1000),fit((i,o),0)/10000,fit((i,o),2)) for i,o in grid]
def trial(r):
    A=[];b=[]
    for i,o,t,e in data:
        A.extend([[-(1+r)*t,-1,-i,-o],[(1-r)*t,1,i,o]])
        b.extend([-(1-r)*e,(1+r)*e])
    sol=linprog([0,0,0,0],A_ub=[[float(x) for x in row] for row in A],b_ub=list(map(float,b)),bounds=[(0,None)]+[(None,None)]*3,method='highs')
    if not sol.success:return None
    k,c,d,h=[Q(f'{x:.12f}') for x in sol.x]
    if k<=0:return None
    need=max(abs(e-k*t-c-d*i-h*o)/(e+k*t) for i,o,t,e in data)
    return (need,k,c,d,h)
lo=Q(0);hi=Q(1,2);cert=trial(hi)
assert cert is not None
for _ in range(24):
    mid=(lo+hi)/2
    v=trial(mid)
    if v is None:lo=mid
    else:
        hi=mid
        if v[0]<cert[0]:cert=v
r,k,c,d,h=cert
errors=[];fix={}
for cell,(i,o,t,e) in zip(grid,data):
    # Signed common fraction achieves the minimum joint relative adjustment here.
    f=(e-k*t-c-d*i-h*o)/(e+k*t)
    tp=t*(1+f);ep=e*(1-f)
    assert ep==k*tp+c+d*i+h*o and max(abs(tp/t-1),abs(ep/e-1))<=r
    fix[cell]=tp,ep;errors.append(str(f))
checked=0
for group in by_total.values():
    for (a,_),(b,_) in combinations(group,2):
        tdiff,ediff=[sum(fix[cell][j] for cell in b)-sum(fix[cell][j] for cell in a) for j in (0,1)]
        assert ediff==k*tdiff
        checked+=1
assert checked==28160
res=dict(table_sha256=sha256(table.encode()).hexdigest(),source=url,compared=checked,radius=str(r),k=str(k),constant=str(c),input_scaled=str(d),output_scaled=str(h),signed_relative_corrections=errors,units='t in 10000 ms, e in Wh, inputs in 100000 tokens, outputs in 1000 tokens',claim='Constructive sufficient bound at nominal coefficients; numerical search, exact rational verification, no optimality claim.')
out=Path('/content/archive.zip')
with zipfile.ZipFile(out,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('common.json',json.dumps(res,indent=2))
print('archive_sha256',sha256(out.read_bytes()).hexdigest())
