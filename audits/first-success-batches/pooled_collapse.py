from math import comb
from fractions import Fraction as F
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
import hashlib,json

def multiply(xs,ys):
    out=[0]*(len(xs)+len(ys)-1)
    for i,x in enumerate(xs):
        for j,y in enumerate(ys):out[i+j]+=x*y
    return out

def run(m):
    n=3; count=[1]; stopped=[1]; ways=[1]
    for a in [75]*(m//2)+[2]*(m//2):
        count=multiply(count,[comb(n,k)*a**k*(100-a)**(n-k) for k in range(n+1)])
        stopped=multiply(stopped,[a*(100-a)**u*100**(n-1-u) for u in range(n)])
        ways=multiply(ways,[1]*n)
    denom=100**(n*m)
    assert sum(count)==denom
    assert sum(stopped)==(100**n-25**n)**(m//2)*(100**n-98**n)**(m//2)
    miss=F(sum(count[:m]),denom)
    scale=10**80
    lo=0
    for s,(mass,number) in enumerate(zip(stopped,ways)):
        lo+=scale*mass*comb(m+s-1,m-1)//(number*denom)
    hi=lo+len(ways)
    beta=F(16,9)*F(2587,3200)**3;alpha=F(2187,3200)
    assert miss<=beta**(m//2) and F(hi,scale)<=alpha**(m//2)
    if m==300:assert beta**150<F(1,1000) and alpha**150<F(1,10**24)
    return dict(batches=m,full_failure_floor80=scale*miss.numerator//miss.denominator,
                score_lower80=lo,score_upper80=hi,common_decimal_scale=80,
                max_rounding_terms=len(ways),full_distribution_total_correct=True)

def main():
    rows=[run(m) for m in (2,10,30,100,300)]
    path=Path('/content/archive.zip')
    with ZipFile(path,'w',ZIP_DEFLATED) as z:z.writestr('collapse.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(path.read_bytes()).hexdigest())
if __name__=='__main__':main()
