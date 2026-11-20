"""Exact labelled-outcome checks for the conditional bias result."""
from fractions import Fraction as F
from itertools import product, combinations_with_replacement
from math import comb, prod
from pathlib import Path
import hashlib, json, zipfile


def check(n, ps):
    m = len(ps)
    t = n*m
    ways = [0]*(t-m+1)
    for waits in product(range(n), repeat=m):
        ways[sum(waits)] += 1
    # Integers for the law; use fractions only after grouping by wait.
    den = prod(p.denominator**n for p in ps)
    law = [0]*(t+1)
    by_wait = [[0]*len(ways) for _ in law]
    for outcomes in product(range(1 << n), repeat=m):
        k = sum(x.bit_count() for x in outcomes)
        weight = prod(p.numerator**x.bit_count()*(p.denominator-p.numerator)**(n-x.bit_count())
                      for p,x in zip(ps,outcomes))
        law[k] += weight
        if all(outcomes):
            s = sum((x & -x).bit_length()-1 for x in outcomes)
            by_wait[k][s] += weight
    assert sum(law) == den
    delta = [F(law[k]*(k>=m),den)-sum(F(y*comb(m+s-1,s),den*ways[s])
            for s,y in enumerate(counts) if y) for k,counts in enumerate(by_wait)]
    assert all(x==0 for x in delta[:m])
    assert all(x>=0 for x in delta[m:m+2])
    assert all(x==0 for x in delta[t-n+1:])
    if n == 2:
        lower = sum((ps[i]-ps[j])**2 * prod(2*p*(1-p) for h,p in enumerate(ps) if h!=i and h!=j)
                    for i in range(m) for j in range(i))
        assert min(delta)>=0 and delta[m]>=lower
        if m==2: assert sum(delta)==lower
        if len(set(ps))==1: assert not any(delta)
        if len(set(ps))>1 and all(0<p<1 for p in ps): assert sum(delta)>0
    return [str(x) for x in delta],str(sum(delta))


from math import factorial
from itertools import combinations

def formula(ps):
    m=len(ps)
    result=[F(0)]*(2*m+1)
    lower=F(0)
    for i,l in combinations(range(m),2):
        rem=[p for a,p in enumerate(ps) if a not in (i,l)]
        gap=(ps[i]-ps[l])**2
        for r in product((0,1,2),repeat=m-2):
            z,h=r.count(0),r.count(2)
            s=r.count(1)
            factor=prod(p**e*(1-p)**(2-e) for p,e in zip(rem,r))
            if not z:
                lower += F(2**s,h+1)*factor*gap
            k=2+sum(r)
            if k<m:continue
            j=z+1
            J=(2*m-k)//2
            profiles=factorial(m-2)//(factorial(z)*factorial(h)*factorial(s))
            count=0
            for t in range(j,J+1):
                doubles=k-m+t
                singles=2*m-k-2*t
                count+=factorial(m)*2**singles//(factorial(t)*factorial(doubles)*factorial(singles))
            result[k]+=F(count,2*comb(m,2)*profiles)*gap*factor
    return result,lower

def main():
    grid=list(map(F,["0","1/4","1/2","3/4","1"]))
    checked={}
    for m in (2,3,4,5,6):
        designs=list(combinations_with_replacement(grid,m)) if m<6 else [tuple(map(F,["1/7","1/4","2/5","3/5","3/4","6/7"]))]
        for ps in designs:
            strata,total=check(2,ps)
            result,lower=formula(ps)
            assert result==list(map(F,strata)) and lower<=F(total)
            if m<=3:assert lower==F(total)
            if m>=4 and all(0<p<1 for p in ps) and len(set(ps))>1:assert lower<F(total)
        checked[str(m)]=len(designs)
    example=list(map(F,["1/4","1/2","3/4"]))
    res,lower=formula(example)
    assert sum(res)==lower==F(57,256)
    path=Path("/content/archive.zip")
    with zipfile.ZipFile(path,"w",zipfile.ZIP_DEFLATED) as z:
        z.writestr("deficit.json",json.dumps(dict(checked=checked,exact_example=str(lower),strata=list(map(str,res)))))
    print("archive_sha256",hashlib.sha256(path.read_bytes()).hexdigest())
if __name__=="__main__":main()
