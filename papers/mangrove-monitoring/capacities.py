from fractions import Fraction as Q
from itertools import product,combinations
from math import prod
from pathlib import Path
import hashlib,json,zipfile
def sym(xs,k):
 co=[1]+[0]*k
 for x in xs:
  for j in range(k,0,-1):co[j]+=x*co[j-1]
 return co[k]
def capped(ms,t):
 lo,hi=0,max(ms)
 while lo<hi:
  mid=(lo+hi+1)//2
  if sum(min(x,mid) for x in ms)<=t:lo=mid
  else:hi=mid-1
 xs=[min(lo,x) for x in ms];rem=t-sum(xs)
 for i,x in enumerate(xs):
  if rem and x<ms[i]:xs[i]+=1;rem-=1
 assert rem==0 and sum(xs)==t
 return xs
K=81618;H=102960;G=16;M=6435;k=13
def risk(ms,t,n):return Q(sym(capped(ms,t),n),sym(ms,n))
def envelope(d,n):
 ms=[M-d]*8+[M+d]*8
 return risk(ms,K,n)
assert envelope(0,k)<=Q(1,20)
lo=0;hi=M-(K+G-1)//G
while lo<hi:
 mid=(lo+hi+1)//2
 if envelope(mid,k)<=Q(1,20):lo=mid
 else:hi=mid-1
assert envelope(lo,k)<=Q(1,20)<envelope(lo+1,k) and M-lo-1>=(K+G-1)//G
cc=0
for ms in ((2,3,4),(1,2,3,4),(1,1,2,5),(2,4,4,5)):
 for n in range(1,len(ms)+1):
  best={}
  for xs in product(*[range(m+1) for m in ms]):
   t=sum(xs);numer=sum(prod(xs[i] for i in I) for I in combinations(range(len(ms)),n));best[t]=max(best.get(t,0),numer)
  for t,y in best.items():assert sym(capped(ms,t),n)==y;cc+=1
# Exhaust the joint maxima over both capacities and survival counts on small even frames.
checked=0
for n in (2,3,4):
 for t in (4,7,8):
  ms0=[2,2,4,4]; assert max(risk(ms,t,n) for ms in product(range(2,5),repeat=4) if sum(ms)==12)==risk(ms0,t,n);checked+=1
ms=[1]*15+[H-15]
res=dict(source='product-of-capacities sampling, one uniformly chosen position per chosen block',K=K,G=G,H=H,k=k,largest_symmetric_tolerance=lo,
 percent_tolerance=str(Q(100*lo,M)),safe=str(envelope(lo,k)),unsafe=str(envelope(lo+1,k)),extremal_capacities=[M-lo]*8+[M+lo]*8,
 counterexample_without_capacity_bounds=dict(capacities=ms,survivors=capped(ms,K),probability=str(risk(ms,K,k))),small_frame_checks=cc,capacity_enumerations=checked)
p=Path('/content/capacities.zip')
with zipfile.ZipFile(p,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('capacities.json',json.dumps(res,indent=2))
print('archive_sha256 '+hashlib.sha256(p.read_bytes()).hexdigest())
