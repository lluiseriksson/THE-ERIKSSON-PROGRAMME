"""Check constructive support transfers at the full-success endpoint, using integer marginals."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from math import factorial,comb,prod
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import json,hashlib


def parts(f,n,lowest=1):
    if f==0:yield ()
    for i in range(lowest,min(f,n)+1):
        for tail in parts(f-i,n,i):yield (i,)+tail


def weights(n,m,f):
    result=[]
    for s in range(f+1):
        c=comb(s+m-1,s)
        ways=sum((-1)**j*comb(m,j)*comb(s-j*n+m-1,m-1) for j in range(min(m,s//n)+1))
        result.append(F(c,ways)-1)
    return result


def check(n,m,f):
    assert m>=f>=n and m*n-f>=m
    ws=weights(n,m,f)
    supply={}
    used=defaultdict(F)
    balanced=F(0)
    for r in parts(f,n):
        d=comb(m,len(r))*(factorial(len(r))//prod(factorial(k) for k in Counter(r).values()))
        if r[-1]==n:
            supply[r]=d*prod(comb(n,j) for j in r)
            continue
        waits=[1]
        for y in r:
            arr=[0]*(len(waits)+y)
            for s,v in enumerate(waits):
                for u in range(y+1):arr[s+u]+=v*comb(n-u-1,y-u)
            waits=arr
        dem=d*sum(v*x for v,x in zip(waits,ws))
        if r[-1]==1:balanced=dem;continue
        donors=list(r[:-1]);t=r[-1]
        while t<n:
            donors[0]-=1;t+=1
            if not donors[0]:donors.pop(0)
        src=tuple(sorted(donors+[t]))
        assert all(sum(sorted(src,reverse=True)[:i])>=sum(r[::-1][:i]) for i in range(1,len(r)+1))
        used[src]+=dem
    assert sum(supply.values())==sum(used.values())+balanced
    load=max((used[r]/v for r,v in supply.items()),default=F(0))
    return dict(n=n,m=m,f=f,max_load=str(load),verified=load<=1)


def main():
    rows=[check(n,m,f) for n in (3,4,5) for m in (16,30,100) for f in range(n,13)]
    for n,f in [(3,6),(4,8),(5,9)]:
        m=2*f**n*(n*(f+2))**(2*(n-2))*(n+1)**(2*n)
        row=check(n,m,f)
        assert row['verified'];rows.append(row)
    p=Path('/content/archive.zip')
    with ZipFile(p,'w',ZIP_DEFLATED) as z:z.writestr('upper-band.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
