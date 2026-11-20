"""Bracket stratum deficits in the failure-odds basis for arbitrary named tilts."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb,prod
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import hashlib,json


@lru_cache(None)
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
    def limiting_ratio(t):
        return (1 + 4*t + 7*t*t) / (12*((1+t)/2)**3)

    pair = limiting_ratio(F(1,2))*limiting_ratio(F(2))
    assert pair == F(5624,6561)
    rows = []
    for m, r in [(4,2),(16,4),(32,6),(64,8),(128,12),(256,16)]:
        odds = [F(1,2), F(2)]*(r//2)
        f = 3*m//2
        lo,hi,scale = intervals(m,3,odds,[f])[f]
        _,poly = weighted_group(3,odds)
        mass = sum(c*choose(3*(m-r),f-y) for y,c in enumerate(poly))
        low, high = 1-F(hi,scale*mass),1-F(lo,scale*mass)
        assert 0 < low <= high < 1
        if m == 4:
            assert low <= 1-brute(m,3,odds)[f]/mass <= high
        digits = 10**12
        rows.append(dict(tasks=m, changed=r, successes=f, denominator=digits,
                         lower=int(low*digits),upper=-(-high*digits//1),
                         asymptotic_pair_factor=str(pair)))
    dest = Path('/content/archive.zip')
    with ZipFile(dest,'w',ZIP_DEFLATED) as zip_file:
        zip_file.writestr('growing-exceptions.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(dest.read_bytes()).hexdigest())

if __name__ == '__main__':
    main()
