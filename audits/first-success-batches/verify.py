"""Exact checks of polynomial unbiasedness, peak weight, and variance ordering."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb,prod
from zipfile import ZipFile,ZIP_DEFLATED
from pathlib import Path
import json,hashlib

def partitions(t,m,lower=1):
    if m==1:
        if t>=lower:yield (t,)
        return
    for j in range(lower,t//m+1):
        for tail in partitions(t-j,m-1,j):
            yield (j,)+tail

def histogram(caps):
    a=[1]
    for n in caps:
        nxt=[0]*(len(a)+n-1)
        for j,k in enumerate(a):
            for u in range(n):nxt[j+u]+=k
        a=nxt
    return a

def weights(caps):
    m=len(caps)
    return [F(comb(m+l-1,m-1),a) for l,a in enumerate(histogram(caps))]

def direct(caps):
    """Count stopped prefixes using full trajectories, and compare conditional means at fixed total."""
    m=len(caps);t=sum(caps);w=weights(caps)
    totals=Counter();seen=Counter()
    for bits in product((0,1),repeat=t):
        start=0;wait=0;hits=0
        for n in caps:
            block=bits[start:start+n];start+=n
            if 1 in block:
                hits+=1;wait+=block.index(1)
        score=w[wait] if hits==m else 0
        totals[sum(bits)]+=score;seen[sum(bits)]+=1
    for k in range(t+1):
        assert seen[k]==comb(t,k)
        assert totals[k]==int(k>=m)*seen[k]

def check():
    count=small=0
    for t in range(1,19):
        for m in range(1,t+1):
            caps=list(partitions(t,m));balanced=caps[-1]
            assert max(balanced)-min(balanced)<=1
            best=histogram(balanced)
            for a in caps:
                h=histogram(a);w=weights(a);count+=1
                assert h[-1]==1 and w[-1]==max(w)==comb(t-1,m-1)
                assert all(x<=y for x,y in zip(h,best))
                assert h==best or any(x<y for x,y in zip(h,best))
                assert (h==best)==(a==balanced)
                if t<=9:
                    direct(a);small+=1
    examples={}
    for a in ((2,2),(4,4,4),(1,1,10),(3,4,5)):
        w=weights(a);p=F(1,2);m=len(a);t=sum(a)
        target=sum(comb(t,k)*p**k*(1-p)**(t-k) for k in range(m,t+1))
        second=p**m*sum(x*y*y*(1-p)**l for l,(x,y) in enumerate(zip(histogram(a),w)))
        assert sum(x*y*p**m*(1-p)**l for l,(x,y) in enumerate(zip(histogram(a),w)))==target
        examples[str(a)]=dict(peak=str(max(w)),variance=str(second-target**2),target=str(target))
    return dict(partitions=count,full_trajectory_comparisons=small,examples=examples)
if __name__=='__main__':
    data=check();p=Path('/content/archive.zip')
    with ZipFile(p,'w',ZIP_DEFLATED) as z:z.writestr('checks.json',json.dumps(data,indent=2))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
