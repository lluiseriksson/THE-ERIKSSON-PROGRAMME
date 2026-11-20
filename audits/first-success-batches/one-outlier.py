"""Check the cubic identity per success stratum using rational arithmetic."""
from fractions import Fraction as F
from itertools import product
from math import comb,prod
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import hashlib,json


def weights(m):
    counts=[1]
    for _ in range(m):
        nxt=[0]*(len(counts)+2)
        for i,c in enumerate(counts):
            for u in range(3):
                nxt[i+u]+=c
        counts=nxt
    return [F(comb(m+s-1,s),c) for s,c in enumerate(counts)]


def direct(m,p,a):
    probs=[a]+[p]*(m-1)
    w=weights(m)
    deficit=[F(0)]*(3*m+1)
    for bits in product((0,1),repeat=3*m):
        k=sum(bits)
        if k<m:
            continue
        mass=prod(v if bit else 1-v for v,block in zip(probs,range(0,3*m,3)) for bit in bits[block:block+3])
        blocks=[bits[i:i+3] for i in range(0,3*m,3)]
        score=w[sum(row.index(1) for row in blocks)] if all(any(row) for row in blocks) else 0
        deficit[k]+=mass*(1-score)
    return deficit


def joint(m,p,a):
    # Conditional on all hits and total wait s, free suffixes are ordinary
    # trials. Separate the exceptional wait to combine homogeneous suffixes.
    w=weights(m)
    counts=[1]
    for _ in range(m-1):
        nxt=[0]*(len(counts)+2)
        for i,c in enumerate(counts):
            for u in range(3): nxt[i+u]+=c
        counts=nxt
    def binprob(n,k,x):
        return comb(n,k)*x**k*(1-x)**(n-k) if 0<=k<=n else 0
    out=[F(0)]*m+[sum(binprob(3,j,a)*binprob(3*(m-1),k-j,p) for j in range(4)) for k in range(m,3*m+1)]
    for s,c in enumerate(counts):
        rem=2*(m-1)-s
        bank=c*p**(m-1)*(1-p)**s
        for u in range(3):
            mass=bank*a*(1-a)**u*w[s+u]
            for j in range(3-u):
                pref=mass*binprob(2-u,j,a)
                for v in range(rem+1):
                    out[m+j+v]-=pref*binprob(rem,v,p)
    return out


def main():
    rows=checks=brutes=0
    for m in (2,3,5,9,17):
        for p in (F(1,5),F(1,2),F(4,5)):
            low,high=joint(m,p,0),joint(m,p,1)
            assert min(low)>=0 and min(high)>=0
            for a in (F(0),F(1,7),p,F(4,7),F(1)):
                obs=joint(m,p,a)
                pred=[(a-p)**2*((1-a)*x/p**2+a*y/(1-p)**2) for x,y in zip(low,high)]
                assert obs==pred and (sum(obs)>0)==(a!=p)
                if m<=3:
                    assert direct(m,p,a)==obs
                    brutes+=1
                rows+=1
                checks+=2*m+1
    dest=Path('/content/archive.zip')
    with ZipFile(dest,'w',ZIP_DEFLATED) as z:
        z.writestr('one-outlier.json',json.dumps(dict(rows=rows,strata=checks,brute_rows=brutes)))
    print('archive_sha256',hashlib.sha256(dest.read_bytes()).hexdigest())


if __name__=='__main__':main()
