"""Certify a diagonal orbit optimum in Q(sqrt(discriminant)), on a pinned scheme."""
import hashlib
import json
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

raw = Path("scheme.json").read_bytes()
assert hashlib.sha256(raw).hexdigest() == "b82a3cef30dacb9ee08be73d13449123bb073716888a081d52bfae0a0205b4ee"
doc = json.loads(raw)
D = 4328**2 - 4*35*24584
K = sp.QQ.algebraic_field(sp.sqrt(D))
def q(x):
    return K.from_sympy(sp.Rational(x))
def expr(x):
    return K.to_sympy(x)
L = K.from_sympy((4328+sp.sqrt(D))/70)
old = list(map(F,doc["meta"]["row_scales"]))
assert old == [1,F(1406919,427109),1,F(204129,422224)]
a = (7595*L-4968)/(2508*L-25320)
b = (1096*L+1472)/(2508*L-25320)
s = [v/q(t) for v,t in zip([K.one,a,K.one,b],old)]
assert all(expr(v).is_positive for v in s)
terms = [defaultdict(F) for _ in range(16)]
def entries(matrix):
    return [(r,c,abs(F(x))) for r,row in enumerate(matrix) for c,x in enumerate(row) if F(x)]
for U,V,W in zip(doc["u"],doc["v"],doc["w"]):
    for i,k,w in entries(W):
        for r,c,u in entries(U):
            for f,h,v in entries(V):
                terms[4*i+k][(r,c,f,h,i,k)] += u*v*w

from itertools import product
from math import lcm, isqrt, comb
import numpy as np
D0=955614
sqrt=sp.sqrt(D0)
atoms=[];den=1
for out,tbl in enumerate(terms):
    groups=defaultdict(lambda:K.zero)
    for (r,c,f,h,i,k),coef in tbl.items():
        ev=[0]*12
        for j,delta in [(r,1),(4+c,-1),(4+f,1),(8+h,-1),(i,-1),(8+k,1)]:ev[j]+=delta
        groups[tuple(ev)]+=q(coef)*s[r]/s[i]
    for ev,v in groups.items():
        u=sp.expand(expr(v));b0=F(u.coeff(sqrt));a0=F(u.subs(sqrt,0))
        assert sp.expand(u-sp.Rational(a0)-sp.Rational(b0)*sqrt)==0
        den=lcm(den,a0.denominator,b0.denominator);atoms.append((out,ev,a0,b0))
signs=np.insert(np.array(list(product((-1,1),repeat=9))),[3,6,9],0,axis=1)
A=np.zeros((16,512,13),dtype=object);B=A.copy();inds=np.arange(512)
for out,ev,a0,b0 in atoms:
    deg=6+signs@ev
    A[out,inds,deg]+=int(a0*den);B[out,inds,deg]+=int(b0*den)
A=A.reshape(-1,13);B=B.reshape(-1,13)
assert len(set(A.sum(axis=1)))==len(set(B.sum(axis=1)))==1
def sign(a,b):
    a,b=int(a),int(b)
    if b==0:return (a>0)-(a<0)
    if a*b>=0:return 1 if b>0 else -1
    delta=a*a-D0*b*b
    return ((delta>0)-(delta<0))*(1 if a>0 else -1)
M=10**26;root=isqrt(D0*M*M)
def signs_exact(a,b):
    est=M*a+b*root
    res=np.where(est>abs(b),1,np.where(est< -abs(b),-1,0))
    for idx in zip(*np.where((res==0)&((a!=0)|(b!=0)))):res[idx]=sign(a[idx],b[idx])
    return res
def column(x,y,k):
    # t=(p+r z)/(q+s z). row k gives transformed coefficients of t^k.
    p,q=x.numerator,x.denominator
    r,s=(1,0) if y is None else (y.numerator,y.denominator)
    coeff=[0]*13
    for i in range(k+1):
        for j in range(13-k):
            coeff[i+j]+=comb(k,i)*comb(12-k,j)*p**(k-i)*r**i*q**(12-k-j)*s**j
    return coeff
def at(t):
    powers=np.array([t.numerator**k*t.denominator**(12-k) for k in range(13)],dtype=object)
    a,b=A@powers,B@powers
    i=int(np.argmax(a*M+b*root))
    ds=signs_exact(a[i]-a,b[i]-b)
    assert min(ds)>=0
    return i
def poly(i):return [[str(a),str(b)] for a,b in zip(A[i],B[i])]
pieces=[];unresolved=[]
def inspect(l,r,depth=0):
    mid=(l+r)/2 if r is not None else l+4
    winners=set(at(t) for t in [mid, (mid+l)/2, (r+mid)/2 if r is not None else l+100])
    T=np.array([column(l,r,k) for k in range(13)],dtype=object)
    AA=A@T;BB=B@T
    alive=np.ones(8192,dtype=bool)
    for w in winners:
        diff=signs_exact(AA[w]-AA,BB[w]-BB)
        alive &= ~((diff.min(axis=1)>=0)&(diff.max(axis=1)>0))
    candidates=list(map(int,np.where(alive)[0]))
    classes={}
    for i in candidates:classes.setdefault(tuple(A[i])+tuple(B[i]),[]).append(i)
    reps=[v[0] for v in classes.values()]
    rec=dict(left=str(l),right=str(r) if r is not None else None,groups=list(classes.values()))
    if len(reps)==1:pieces.append(rec);return
    if len(reps)==2:
        i,j=reps;ds=signs_exact(AA[i]-AA[j],BB[i]-BB[j]);ss=[int(v) for v in ds if v]
        if sum(u!=v for u,v in zip(ss,ss[1:]))==1:
            rec.update(first=i if ss[0]>0 else j,last=i if ss[-1]>0 else j,root='one');pieces.append(rec);return
    if depth>=5:unresolved.append(rec);return
    inspect(l,mid,depth+1);inspect(mid,r,depth+1)
for l,r in [(1,2),(2,4),(4,8),(8,None)]:inspect(F(l),None if r is None else F(r))
chosen={i for piece in pieces+unresolved for group in piece['groups'] for i in group}
out=dict(field=D0,den=str(den),count=8192,pieces=pieces,unresolved=unresolved,profiles={i:dict(output=i//512,signs=signs[i%512].tolist(),numerator=poly(i)) for i in chosen})


def gaps(i,j,t):
    h=[t.numerator**k*t.denominator**(12-k) for k in range(13)]
    return sign(sum(v*x for v,x in zip(A[i]-A[j],h)),sum(v*x for v,x in zip(B[i]-B[j],h)))
from itertools import combinations
crossings=[]
def compare(i,j,l,r,depth=0):
    T=np.array([column(l,r,k) for k in range(13)],dtype=object)
    ss=[x for x in signs_exact((A[i]-A[j])@T,(B[i]-B[j])@T) if x]
    variations=sum(a!=b for a,b in zip(ss,ss[1:]))
    if not variations:return
    if variations==1:
        orient=int(ss[0])
        for _ in range(64):
            mid=(l+r)/2
            side=gaps(i,j,mid)*orient
            if side==0:
                l=r=mid;break
            if side>0:l=mid
            else:r=mid
        crossings.append(dict(i=i,j=j,bracket=[str(l),str(r)],approximate=float((l+r)/2)))
        return
    if depth>=22:raise ValueError(('root count',i,j,ss,l,r))
    mid=(l+r)/2
    if gaps(i,j,mid)==0:crossings.append(dict(i=i,j=j,bracket=[str(mid)]*2,approximate=float(mid)))
    compare(i,j,l,mid,depth+1);compare(i,j,mid,r,depth+1)
for rec in pieces+unresolved:
    for x,y in combinations(rec['groups'],2):
        compare(x[0],y[0],F(rec['left']),F(rec['right']))
crossings.sort(key=lambda d:F(d['bracket'][0]))
def best(t):
    i=at(t);qv=np.array([t.numerator**k*t.denominator**(12-k) for k in range(13)],dtype=object)
    aa=A@qv;bb=B@qv
    return list(map(int,np.where(signs_exact(aa[i]-aa,bb[i]-bb)==0)[0]))
events=[]
for n,pair in enumerate(crossings):
    l,r=map(F,pair['bracket'])
    before=F(crossings[n-1]['bracket'][1]) if n else F(1)
    after=F(crossings[n+1]['bracket'][0]) if n+1<len(crossings) else r+1
    if before>=l or after<=r:raise ValueError(('coincident root',crossings))
    events.append(dict(**pair,before=best((l+before)/2),after=best((r+after)/2)))
out['events']=events
out['endpoints']={v:best(F(v)) for v in {d[k] for d in pieces+unresolved for k in ['left','right'] if d[k] not in [None,'1']}}
print(json.dumps(out))
