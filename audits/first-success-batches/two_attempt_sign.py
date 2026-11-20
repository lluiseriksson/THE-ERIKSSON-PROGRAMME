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


def main():
    grid=list(map(F,["0","1/4","1/2","3/4","1"]))
    counts={}
    for n,m in [(2,2),(2,3),(2,4),(2,5),(3,2),(3,3),(4,2)]:
        count=0
        for ps in combinations_with_replacement(grid,m):
            check(n,ps)
            count+=1
        counts[f"{n}x{m}"]=count
    ps=list(map(F,["1/4","1/2","3/4"]))
    strata,gap=check(2,ps)
    report=dict(designs=counts,example=dict(p=list(map(str,ps)),stratum_deficits=strata,full_minus_score=gap))
    path=Path("/content/archive.zip")
    with zipfile.ZipFile(path,"w",zipfile.ZIP_DEFLATED) as z:
        z.writestr("two-attempt.json",json.dumps(report,indent=2))
    print("archive_sha256",hashlib.sha256(path.read_bytes()).hexdigest())
if __name__=="__main__": main()
