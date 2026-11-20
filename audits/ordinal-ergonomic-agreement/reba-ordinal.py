"""Attainable directed threshold-error profiles for ordered categories."""
from collections import Counter
from itertools import product
from fractions import Fraction as F
import json

def cuts(i,j,k):
    return tuple(int(i>t>=j) for t in range(k-1))+tuple(int(j>t>=i) for t in range(k-1))

def bounds(profile):
    """Minimum and maximum counts of nonempty intervals with these heights."""
    start_count=sum(max(0,b-a) for a,b in zip((0,*profile),profile))
    return start_count,sum(profile)

def attainable(vector,e):
    k=len(vector)//2
    l1,h1=bounds(vector[:k]);l2,h2=bounds(vector[k:])
    return l1+l2<=e<=h1+h2

def brute(k,e):
    states={(0,)*(2*(k-1))}
    increments={cuts(i,j,k) for i in range(k) for j in range(k) if i!=j}
    for _ in range(e):
        states={tuple(a+b for a,b in zip(v,w)) for v in states for w in increments}
    return states

def construct(n,e,v):
    k=len(v)//2+1
    families=[]
    for rev,seq in enumerate([v[:k-1],v[k-1:]]):
        for height in range(1,max(seq,default=0)+1):
            start=None
            for t,val in enumerate((*seq,0)):
                if val>=height and start is None:start=t
                if val<height and start is not None:
                    families.append((start,t,rev))
                    start=None
    while len(families)<e:
        i=next(i for i,(a,b,r) in enumerate(families) if b>a+1)
        a,b,r=families.pop(i)
        families.extend([(a,a+1,r),(a+1,b,r)])
    mat=Counter({(0,0):n-e})
    for a,b,up in families:mat[(a,b) if up else (b,a)]+=1
    check=tuple(sum(w*cuts(i,j,k)[t] for (i,j),w in mat.items()) for t in range(2*(k-1)))
    if check!=v or sum(mat.values())!=n or sum(w for (i,j),w in mat.items() if i!=j)!=e:
        raise ValueError('Bad witness')
    return {f'{i},{j}':w for (i,j),w in sorted(mat.items()) if w}
out=[]
for k in range(2,6):
    for e in range(4):
        actual=brute(k,e)
        computed={v for v in product(range(e+1),repeat=2*(k-1)) if attainable(v,e)}
        if actual!=computed:raise ValueError((k,e))
        for v in computed:construct(132,e,v)
        out.append([k,e,len(actual)])
matches=[c for c in range(133) if F(835,10)<=F(100*c,132)<F(845,10)]
if matches!=[111]:raise ValueError(matches)
cases={}
for name,a in [('all_adjacent',(0,21,0,0,0,0,0,0)),('all_four',(21,21,21,21,0,0,0,0)),('alternating',(21,0,21,0,0,0,0,0)),('same_lower_two_cuts',(10,10,0,0,0,0,0,0)),('flat_both',(3,7,7,2,0,6,7,4))]:
    ok=attainable(a,21)
    cases[name]=dict(profile=a,feasible=ok,witness=construct(132,21,a) if ok else None)
print(json.dumps(dict(matches=matches,discordant=21,small_checks=out,cases=cases),indent=2))
