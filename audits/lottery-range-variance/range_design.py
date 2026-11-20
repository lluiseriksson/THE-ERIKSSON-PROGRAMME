"""Exact attainable variance versus distinguishability from the uniform ticket lottery."""
from collections import Counter
from fractions import Fraction as Q
from itertools import accumulate,combinations_with_replacement,product
from pathlib import Path
from hashlib import sha256
import json,zipfile

def mass_terms(x):
    n=len(x);l=n-1;freq=Counter(x);cs=[0]+list(accumulate(freq[i] for i in range(n)))
    out=[Counter() for _ in range(n)]
    for lo in range(n):
        out[0][freq[lo]]+=1
        for hi in range(lo+1,n):
            m=out[hi-lo]
            m[cs[hi+1]-cs[lo]]+=1
            m[cs[hi]-cs[lo]]-=1
            m[cs[hi+1]-cs[lo+1]]-=1
            m[cs[hi]-cs[lo+1]]+=1
    return [{k:v for k,v in t.items() if k and v} for t in out]
def counts(terms,m):
    return [sum(v*k**m for k,v in t.items()) for t in terms]
def gap_key(x):
    n=len(x);g=[b-a for a,b in zip(x,x[1:])]
    return tuple(g[i]+g[-1-i] for i in range(n//2-1))+(g[n//2-1],)
def designs(n):
    h=n//2
    for inc in product((-1,0,1),repeat=h-1):
        s=(0,*accumulate(inc))
        if sum(s):continue
        yield tuple(j+(s[j] if j<h else s[n-1-j]) for j in range(n))
def record(x,n,base):
    terms=mass_terms(x);l=n-1
    excess=Q(sum((2*v-l)**2 for v in x)-sum((2*v-l)**2 for v in range(n)),4*n)
    assert excess>=0
    best=Q(0);peak=[];tv2=None
    if not excess:return dict(x=x,excess='0',tv2='0',max_tv='0',peaks=[],last=0)
    for m in range(2,1001):
        a,b=counts(terms,m),counts(base,m);den=n**m
        assert min(a)>=0 and sum(a)==sum(b)==den
        assert sum(k*(z-w) for k,(z,w) in enumerate(zip(a,b)))==0
        if m==2:
            obs=Counter(abs(s-t) for s in x for t in x)
            assert a==[obs[k] for k in range(n)]
        tv=Q(sum(abs(z-w) for z,w in zip(a,b)),2*den)
        if m==2:tv2=tv;assert tv>=2*excess/(l*l//4)
        if tv>best:best=tv;peak=[m]
        elif tv==best:peak.append(m)
        if 2*Q(n-1,n)**(m+1)<best:break
    else:raise RuntimeError('tail bound did not certify maximum')
    return dict(x=x,excess=str(excess),tv2=str(tv2),max_tv=str(best),peaks=peak,last=m)

def skyline(rows,key):
    points={(Q(r['excess']),Q(r[key])) for r in rows}
    return [dict(excess=str(v),tv=str(t),example=next(r for r in rows if Q(r['excess'])==v and Q(r[key])==t)) for v,t in sorted(points)
            if not any(w>=v and s<=t and (w,s)!=(v,t) for w,s in points)]
out={}
for n in (8,10,12,14,16):
    xs=list(designs(n));key=gap_key(range(n))
    assert len(xs)==len(set(xs)) and all(x==tuple(sorted(x)) and x[0]==0 and x[-1]==n-1 and 2*sum(x)==n*(n-1) and gap_key(x)==key for x in xs)
    if n<=10:
        assert set(xs)=={(0,*mid,n-1) for mid in combinations_with_replacement(range(n),n-2) if 2*(sum(mid)+n-1)==n*(n-1) and gap_key((0,*mid,n-1))==key}
    rows=[record(x,n,mass_terms(range(n))) for x in xs]
    out[n]=dict(designs=len(xs),vs_two=skyline(rows,'tv2'),vs_all=skyline(rows,'max_tv'),rows=rows)
p=Path('/content/archive.zip')
with zipfile.ZipFile(p,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('stimuli.json',json.dumps(out))
print('archive_sha256',sha256(p.read_bytes()).hexdigest())
