from fractions import Fraction as Q
from itertools import combinations
from math import comb
from pathlib import Path
import json,zipfile,hashlib
G=16;M=6435;K=81618;alpha=Q(1,20)
def curve(g,m,t,a):
 q=t//m
 rows=[]
 for d in range(1,g+1):
  p=Q(comb(q,d),comb(g,d)) if d<=q else Q(0)
  beta=min(Q(1),a/p) if p else Q(1)
  rows.append(dict(d=d,null_all_full=str(p),sharp_full_power=str(beta),size=str(p*beta)))
 return rows
rows=curve(G,M,K,alpha)
assert rows[0]['sharp_full_power']=='1/15'
assert Q(rows[6]['sharp_full_power'])<Q(4,5) and Q(rows[7]['sharp_full_power'])==1
checked=0
# Verify incidence counts directly both over uniformly random full blocks and over test footprints.
for g in range(2,9):
 for q in range(g):
  S=list(combinations(range(g),q))
  for d in range(1,g+1):
   D=list(combinations(range(g),d))
   p=Q(comb(q,d) if q>=d else 0,comb(g,d))
   v=[[set(a)<=set(b) for b in S] for a in D]
   assert all(Q(sum(row),len(S))==p for row in v)
   assert all(Q(sum(row[j] for row in v),len(D))==p for j in range(len(S)))
   checked+=1
out=Path('/content/footprint.zip')
with zipfile.ZipFile(out,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('footprint.json',json.dumps(dict(G=G,M=M,K=K,alpha=str(alpha),positive='all positions in accessible frame established',rows=rows,incidence_grid_checks=checked),indent=2))
print('archive_sha256 '+hashlib.sha256(out.read_bytes()).hexdigest())
