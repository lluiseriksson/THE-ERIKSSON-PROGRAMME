from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json, subprocess
rows=[r for r in json.loads(Path('tables.json').read_bytes())['S3.T1'] if r['section']=='vision']
targets=[[int(10*F(row['values'][k])) for k in (0,1,2,6,7,8)] for row in rows]
subprocess.run(['g++','-std=c++17','-O2','repair_ranges.cpp','-o','repair_ranges'],check=True)
output=subprocess.check_output(['./repair_ranges'],input=''.join(' '.join(map(str,row))+'\n' for row in targets).encode()).decode().splitlines()
eps=F(1,10**8)
def check(w,bins):
    t,u,c,d,x,y=w
    if not (0<=c<=t<=376 and 0<=d<=u<=266 and 0<=x<=354 and 0<=y<=233):raise ValueError(w)
    for a,b,expected in ((t,u,bins[:3]),(c,d,bins[3:])):
        p=500*(a/(a+x+eps)+b/(b+y+eps))
        r=500*(a/(376+eps)+b/(266+eps))
        if not all(abs(v-e)<F(1,2) for v,e in zip((p,r,2*p*r/(p+r)),expected)):raise ValueError(w)
    return F(c+d,t+u)
intervals={};cert={}
for row,bins,line in zip(rows,targets,output,strict=True):
    n,*counts=map(int,line.split())
    low,high=counts[:6],counts[6:]
    l,h=check(low,bins),check(high,bins)
    if n<1 or l>h:raise ValueError(row['model'])
    name=row['model'];intervals[name]=(l,h)
    cert[name]=dict(assignments=n,lower=str(l),upper=str(h),witness_lower=low,witness_upper=high)
groups={'strict':[],'reversible':[],'touching':[]}
for a,b in combinations(intervals,2):
    l,h=intervals[a];v,w=intervals[b]
    if h<v:groups['strict'].append([b,a])
    elif w<l:groups['strict'].append([a,b])
    elif l<w and v<h:groups['reversible'].append([a,b])
    else:groups['touching'].append([a,b])
print(json.dumps(dict(models=cert,pairs=groups)))