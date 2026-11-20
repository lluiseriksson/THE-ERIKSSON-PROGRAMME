"""Exact zero-detection envelope for fractional-interval equal-probability systematic samples."""
from itertools import combinations
from math import gcd,comb,ceil
from fractions import Fraction
import json
def samples(N,n):
    # Uniform U in [0,N/n). U=(s+delta)/n, s=0..N-1, 0<=delta<1.
    return [frozenset((s+j*N)//n for j in range(n)) for s in range(N)]
def envelope(N,n,m):
    if m==0:return Fraction(1)
    g=gcd(N,n);L=N//g;d=n//g
    return Fraction(max(0,L-d-(m+g-1)//g+1),L)
def witness(N,n,m):
    # Unit i covers phases starting at (i*n mod N)/g, each repeated g times.
    return sorted(range(N),key=lambda i:((i*n)%N,i))[:m]
def trial(N,n,ms,exhaust):
    ss=samples(N,n);assert all(len(x)==n for x in ss)
    for m in ms:
        P=set(witness(N,n,m))
        got=sum(not (P&s) for s in ss);assert Fraction(got,N)==envelope(N,n,m)
        if exhaust:
            other=max(sum(s.isdisjoint(p) for s in ss) for p in combinations(range(N),m))
            assert other==got
    return len(ms)
def main():
    checked=sum(trial(N,n,range(N+1),True) for N in range(1,13) for n in range(1,N+1))
    N,n=127,32;trial(N,n,range(N+1),False);p=envelope(N,n,62)
    census=3;outside=16;needed=81-census-outside
    assert needed==62
    B_negative=11;pos_unseen=N-n-B_negative
    z=set(witness(N,n,pos_unseen));truth=set(range(N))-z
    # Fix high priority in advance for the 43 negatives in this counterexample.
    order=sorted(range(N),key=lambda i:(i not in truth,i));samp=samples(N,n)
    jointly_missed=sum(s.isdisjoint(z) and set([i for i in order if i not in s][:11]).isdisjoint(z) for s in samp)
    assert Fraction(jointly_missed,N)==envelope(N,n,84)
    res=dict(small_triples=checked,application=dict(N=N,n=n,confidence_upper_zero=max(m for m in range(N+1) if envelope(N,n,m)>Fraction(1,20)),single_stage_deterministic_max=pos_unseen,joint_miss_84=str(Fraction(jointly_missed,N)),assembly_max=pos_unseen+census+outside,threshold_for_population_majority=needed,miss_62=str(p),srs_miss_62=str(Fraction(comb(N-62,n),comb(N,n))),miss_62_independent=[str(p**r) for r in (1,2,3)],targeted_extra_negative_to_exclude_majority=103-80))
    print(json.dumps(res,sort_keys=True,indent=2))
if __name__=='__main__':main()