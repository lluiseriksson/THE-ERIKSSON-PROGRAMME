"""Bracket stratum deficits in the failure-odds basis for arbitrary named tilts."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb,prod
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import hashlib,json


def choose(n,k):
    return comb(n,k) if 0<=k<=n else 0


@lru_cache(None)
def cap(m,n,s):
    if s<0 or s>m*(n-1):return 0
    return sum((-1)**j*comb(m,j)*comb(m+s-n*j-1,m-1) for j in range(min(m,s//n)+1))


def weighted_group(n,ts):
    paths={(0,0):1}
    full=[1]
    for t in ts:
        a,b=t.numerator,t.denominator
        nxt={}
        poly=[0]*(len(full)+n)
        for j in range(n+1):
            fac=a**j*b**(n-j)
            for k,c in enumerate(full):
                poly[k+j]+=c*comb(n,j)*fac
            for u in range(min(j,n-1)+1):
                coeff=choose(n-1-u,j-u)*fac
                if not coeff: continue
                for (y,v),c in paths.items():
                    key=(y+j,v+u)
                    nxt[key]=nxt.get(key,0)+c*coeff
        paths,full=nxt,poly
    return paths,full


def intervals(m,n,ts,fs):
    r=len(ts);paths,full=weighted_group(n,ts)
    scale=(1<<(m*n+65))*prod(max(t.numerator,t.denominator)**n for t in ts)
    ws=[divmod(scale*comb(m+i-1,i),cap(m,n,i)) for i in range(min(max(fs),(n-1)*m)+1)]
    out={}
    for f in fs:
        actual=sum(c*choose((m-r)*n,f-y) for y,c in enumerate(full))
        lower=upper=actual*scale
        for (y,u),c in paths.items():
            for v in range(min(f-y,(m-r)*(n-1))+1):
                mult=c*cap(m-r,n,v)*choose((m-r)*(n-1)-v,f-y-v)
                q,rem=ws[v+u]
                lower-=mult*(q+bool(rem));upper-=mult*q
        out[f]=(lower,upper,scale)
    return out


def brute(m,n,ts):
    ans=[F(0)]*(m*(n-1)+1)
    for bits in product((0,1),repeat=m*n):
        f=sum(bits)
        if f>=len(ans):continue
        blocks=[bits[i:i+n] for i in range(0,m*n,n)]
        mult=prod(t.numerator**sum(g)*t.denominator**(n-sum(g)) for t,g in zip(ts,blocks))
        z=0
        if all(0 in g for g in blocks):
            s=sum(g.index(0) for g in blocks)
            z=F(comb(m+s-1,s),cap(m,n,s))
        ans[f]+=mult*(1-z)
    return ans


def main():
    summary=dict(positive=0,identity=0,unresolved=[],negative=[],enumerated=0,banks=0)
    cases=[(3,3),(4,3),(4,4),(9,3),(17,4),(32,5),(64,4),(128,3)]
    for m,n in cases:
        for ts in [(F(1),F(1)),(F(1,5),F(9)),(F(0),F(m*m)),(F(1,2),F(2)),
                   (1-F(1,m**3),1+F(1,m**3)),(F(m*m),F(m**3)),
                   (F(1,7),1+F(1,m),F(3*m))]:
            if len(ts)>=m:continue
            fs=list(range((n-1)*m+1)) if m<=9 else sorted({0,n-1,n,n+1,2*n,m//2,m,(n-1)*m-1,(n-1)*m})
            bounds=intervals(m,n,ts,fs)
            exact=brute(m,n,ts) if m*n<=12 else None
            summary['banks']+=1
            for f,(lo,hi,scale) in bounds.items():
                if exact is not None:
                    assert lo<=exact[f]*scale<=hi
                    summary['enumerated']+=1
                if f<n or all(t==1 for t in ts):
                    assert lo<=0<=hi
                    summary['identity']+=1
                elif lo>0:summary['positive']+=1
                else:
                    key='negative' if hi<0 else 'unresolved'
                    summary[key].append([m,n,list(map(str,ts)),f])
    dest=Path('/content/archive.zip')
    with ZipFile(dest,'w',ZIP_DEFLATED) as z:z.writestr('individual-odds.json',json.dumps(summary))
    print('archive_sha256',hashlib.sha256(dest.read_bytes()).hexdigest())


if __name__=='__main__':main()
