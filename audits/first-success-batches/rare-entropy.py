"""Check the rare-tail equivalent against integer enclosures in two-class banks."""
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import comb, lcm
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import json, hashlib


def multiply(a,b):
    c=[0]*(len(a)+len(b)-1)
    for j,v in enumerate(a):
        for k,w in enumerate(b):c[j+k]+=v*w
    return c


def power(base,h):
    a=[base[0]**h]
    for s in range(1,h*(len(base)-1)+1):
        v,rem=divmod(sum(((h+1)*j-s)*base[j]*a[s-j]
                         for j in range(1,min(len(base)-1,s)+1)),s*base[0])
        assert rem==0 and v>0
        a.append(v)
    assert sum(a)==sum(base)**h
    return a


def check(m,n,pa,pb):
    den=lcm(pa.denominator,pb.denominator)
    x,y=int(den*pa),int(den*pb)
    f,g=den-x,den-y
    h=m//2
    full=power([f*g,x*g+y*f,x*y],h*n)
    target=sum(full[m:])
    stop=power(multiply([f**j for j in range(n)],[g**j for j in range(n)]),h)
    cap=power([1]*n,m)
    scale=10**31
    lo=hi=0
    base=(x*y)**h*den**(m*(n-1))
    unbound=1
    for s,v in enumerate(stop):
        k,r=divmod(base*v*unbound*scale,cap[s]*target)
        lo+=k;hi+=k+bool(r)
        if s<len(stop)-1:base//=den
        unbound=unbound*(m+s)//(s+1)
    with localcontext() as ctx:
        ctx.prec=55
        a=Decimal(1)/n
        u,v=[Decimal(t)/den for t in (x,y)]
        left,right=Decimal(1),Decimal(1)
        def tilt(t,k):return k*t/(1-t+k*t)
        while (tilt(u,right)+tilt(v,right))/2<a:right*=2
        for _ in range(180):
            mid=(left+right)/2
            if (tilt(u,mid)+tilt(v,mid))/2<a:left=mid
            else:right=mid
        lam=(left+right)/2
        t,z=tilt(u,lam),tilt(v,lam)
        meanvar=(t*(1-t)+z*(1-z))/2
        stopden=1-(1-a)*(1/(1-u)+1/(1-v))/2
        pref=a*(1-1/lam)/stopden*(meanvar/(a*(1-a))).sqrt()
        unit=lambda k: (k/a)*((1-k)/(1-a))**(n-1)
        equiv=pref*(unit(t)*unit(z))**h
        if pa==pb:
            assert lo<=scale<=hi and abs(equiv-1)<Decimal('1e-45')
        assert lo>0
        return dict(m=m,n=n,p=[str(pa),str(pb)],scale=scale,lower=lo,upper=hi,equivalent=str(equiv))
    

def main():
    rows=[]
    for k in (4,8,16,24):
        for pair in [(F(1,6),F(1,4)),(F(1,4)-F(1,8*k),F(1,4)+F(1,8*k)),(F(1,5),F(1,5))]:
            rows.append(check(k*k,3,*pair))
    dest=Path('/content/archive.zip')
    with ZipFile(dest,'w',ZIP_DEFLATED) as z:z.writestr('rare-entropy.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(dest.read_bytes()).hexdigest())


if __name__=='__main__':main()
