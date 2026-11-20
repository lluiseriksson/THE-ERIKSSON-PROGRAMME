from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb,prod
from pathlib import Path
from zipfile import ZipFile
import hashlib,json

@lru_cache(None)
def multiplicities(m,n):
    v=[1]
    for _ in range(m):
        w=[0]*(len(v)+n-1)
        for i,c in enumerate(v):
            for u in range(n):w[i+u]+=c
        v=w
    return v

def score_mean(ps,n):
    m=len(ps);caps=multiplicities(m,n)
    return sum(F(comb(m+sum(us)-1,m-1),caps[sum(us)])*prod(p*(1-p)**u for p,u in zip(ps,us)) for us in product(range(n),repeat=m))

def full(ps,n):
    mass=[F(1)]
    for p in ps:
        for _ in range(n):
            new=[F(0)]*(1+len(mass))
            for i,v in enumerate(mass):new[i]+=v*(1-p);new[i+1]+=v*p
            mass=new
    return mass

def main():
    checks=0
    for n in range(2,9):
        for j in range(1,11):
            a=multiplicities(j,n);b=multiplicities(j+1,n)
            for s,old in enumerate(a):
                assert old*comb(j+s,j)<=b[s]*comb(j+s-1,j-1);checks+=1
    cases=0
    for k,n,r in ((1,3,2),(2,3,1),(3,2,1),(3,3,2)):
        for ps in product((F(1,4),F(3,4)),repeat=k):
            mass=full(ps,n); base=sum(mass[k:])-score_mean(ps,n)
            extra=sum(mass[max(0,k-r*(n-1)):k])
            pp=ps+(F(1),)*r
            new=sum(full(pp,n)[k+r:])-score_mean(pp,n)
            assert new>=base+extra
            for err in (F(1,4096),F(1,8)):
                pp=ps+(1-err,)*r
                changed=sum(full(pp,n)[k+r:])-score_mean(pp,n)
                bound=(1+comb((k+r)*n-1,k+r-1))*(1-(1-err)**(n*r))
                assert changed>=base+extra-bound
            cases+=1
    out=Path('/content/archive.zip')
    with ZipFile(out,'w') as z:z.writestr('certain.json',json.dumps(dict(composition_checks=checks,designs=cases)))
    print('archive_sha256',hashlib.sha256(out.read_bytes()).hexdigest())
if __name__=='__main__':main()
