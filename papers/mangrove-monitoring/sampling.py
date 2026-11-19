from fractions import Fraction as Q
from math import comb,prod
from itertools import combinations,product
from pathlib import Path
import json,hashlib,zipfile
G=16;M=6435;N=125269;A=401564900;B=616326000
K=A*N//B
def choose(n,r):return comb(n,r) if 0<=r<=n else 0
def simple(n,t,k):return Q(choose(t,k),choose(n,k))
def spread(g,m,t,k):
 a,r=divmod(t,g)
 return Q(sum(choose(r,i)*choose(g-r,k-i)*(a+1)**i*a**(k-i) for i in range(k+1)),comb(g,k)*m**k)
def one(g,m,t,k):
 q,r=divmod(t,m)
 return (q+simple(m,r,k))/g
def below(x):return x<=Q(1,20)
def evaluate(k):return [simple(N,K,k),simple(G*M,K,k),spread(G,M,K,k),one(G,M,K,k)]
assert K==81618 and K<G*M
rows={k:evaluate(k) for k in range(1,G+1)}
first=[next((k for k,row in rows.items() if below(row[i])),None) for i in range(4)]
assert first==[7,13,13,None] and rows[13][3]>Q(3,4)
# Independent check of the balanced worst case via repeated polynomial multiplication.
xs=[K//G+(i<K%G) for i in range(G)]
co=[1]
for x in xs:co=[a+b for a,b in zip(co+[0],[0]+[v*x for v in co])]
for k,o in rows.items():assert o[2]==Q(co[k],comb(G,k)*M**k)
# Enumerate *every* labelled landscape for small complete frames.
checks=0
for g,m in [(3,3),(4,3),(3,4)]:
 for k in range(1,min(g,m)+1):
  bounds={}
  for xs in product(range(m+1),repeat=g):
   t=sum(xs)
   vals=(Q(sum(prod(xs[i] for i in I) for I in combinations(range(g),k)),comb(g,k)*m**k),sum(simple(m,x,k) for x in xs)/g)
   old=bounds.get(t,(0,0));bounds[t]=tuple(max(a,b) for a,b in zip(old,vals))
  for t,(a,b) in bounds.items():
   assert a==spread(g,m,t,k) and b==one(g,m,t,k);checks+=1
out={'k0':K,'groups':G,'capacity':M,'by_sample_size':{k:list(map(str,v)) for k,v in rows.items()},'first_at_0.05':first,'small_frame_checks':checks,'balanced':[K//G,K%G],'concentrated':list(divmod(K,M)),'scope':'one prespecified final all-established test; complete equal frames; one fixed horizon'}
p=Path('/content/sampling.zip')
with zipfile.ZipFile(p,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('sampling.json',json.dumps(out,indent=2))
print('archive_sha256 '+hashlib.sha256(p.read_bytes()).hexdigest())
