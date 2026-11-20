"""Compare a stopped mean to the full tail on a bank with a fixed exceptional set."""
from fractions import Fraction as F
from itertools import product
from math import comb, prod
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import json, hashlib


def multiply(a, b):
    c = [0]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b):
            c[j+k] += x*y
    return c


def capped(m,n):
    coeff=[1]
    for s in range(1,m*(n-1)+1):
        value=sum(((m+1)*j-s)*coeff[s-j] for j in range(1,min(n-1,s)+1))
        v,rem=divmod(value,s)
        assert rem==0 and v>0
        coeff.append(v)
    assert coeff==coeff[::-1] and sum(coeff)==n**m
    return coeff


def enclosing(m,n,p,fail,scale):
    rest=m-len(fail)
    total=n*rest
    b,d=p.numerator,p.denominator
    a=d-b
    f=[1]
    stopped=[1]
    for x in fail:
        den=x.denominator
        miss=x.numerator
        hit=den-miss
        f=multiply(f,[comb(n,j)*hit**j*miss**(n-j) for j in range(n+1)])
        stopped=multiply(stopped,[hit*miss**j*den**(n-1-j) for j in range(n)])
    full_rest=[comb(total,j)*b**j*a**(total-j) for j in range(total+1)]
    right=0
    for j in reversed(range(len(full_rest))):
        right+=full_rest[j];full_rest[j]=right
    target=sum(c*full_rest[max(0,m-k)] for k,c in enumerate(f) if m-k<=total)
    assert target>0
    table=capped(m,n); free=capped(rest,n)
    unlimited=[1]
    for s in range(1,len(table)):
        unlimited.append(unlimited[-1]*(m+s-1)//s)
    lower=upper=0
    for s,v in enumerate(free):
        rest_mass=b**rest*a**s*d**(total-rest-s)*v
        for j,value in enumerate(stopped):
            k=s+j
            quotient,rem=divmod(scale*value*rest_mass*unlimited[k],target*table[k])
            lower+=quotient;upper+=quotient+bool(rem)
    return dict(tasks=m,cap=n,p=str(p),exceptions=[str(x) for x in fail],scale=scale,lower=lower,upper=upper)


def brute(m,n,p,fail):
    probs=[p]*(m-len(fail))+[1-x for x in fail]
    result=target=F(0)
    for bits in product((0,1),repeat=m*n):
        weight=prod((v if bit else 1-v) for i,v in enumerate(probs) for bit in bits[n*i:n*i+n])
        if sum(bits)>=m:target+=weight
        blocks=[bits[n*i:n*i+n] for i in range(m)]
        if all(any(t) for t in blocks):
            s=sum(t.index(1) for t in blocks)
            allowed=sum(sum(row)==s for row in product(range(n),repeat=m))
            result+=weight*F(comb(m+s-1,s),allowed)
    return result/target


def main():
    scale=10**22
    small=0
    for n in (2,3):
        for xx in ([F(0)],[F(1,7)],[F(0),F(1,5)],[F(1)]):
            r=enclosing(3,n,F(1,n+1),xx,scale)
            exact=brute(3,n,F(1,n+1),xx)
            assert r['lower']<=scale*exact<=r['upper']
            small+=1
    rows=[]
    for m in (16,64,256,1024):
        for n,p in [(2,F(1,4)),(2,F(1,2)),(3,F(1,6)),(3,F(1,3))]:
            rows.append(enclosing(m,n,p,[F(0)],scale))
        rows.append(enclosing(m,3,F(1,6),[F(1,m)],scale))
    dest=Path('/content/archive.zip')
    with ZipFile(dest,'w',ZIP_DEFLATED) as z:
        z.writestr('exceptional-tasks.json',json.dumps(dict(exhaustive=small,rows=rows)))
    print('archive_sha256',hashlib.sha256(dest.read_bytes()).hexdigest())


if __name__=='__main__':main()
