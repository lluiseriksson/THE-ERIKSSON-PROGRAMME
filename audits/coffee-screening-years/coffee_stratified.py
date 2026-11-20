"""Randomization inference conditional on the pilot's year-stratum sizes."""
from fractions import Fraction as F
from math import comb
import json
def c(n,k):return comb(n,k) if 0<=k<=n else 0
def calc(row):
    N,M=row['population'];x,z=row['pilot_recent'];y,t=row['pilot_early'];n=x+z;m=y+t
    threshold=N*x*m-M*y*n;den=c(N,n)*c(M,m)
    p0=[[c(a,i)*c(N-a,n-i) for i in range(n+1)] for a in range(N+1)]
    cum=[]
    for b in range(M+1):
        acc=[0]
        for j in range(m+1):acc.append(acc[-1]+c(b,j)*c(M-b,m-j))
        cum.append(acc)
    limits=[max(0,min(m+1,1+(N*i*m-threshold)//(M*n))) for i in range(n+1)]
    def worst(d):
        poss=[(sum(h*cum[max(0,a-d)][k] for h,k in zip(probs,limits)),a,max(0,a-d)) for a,probs in enumerate(p0) if max(0,a-d)<=M]
        return max(poss) if poss else (0,None,None)
    lo,hi=-M-1,N
    while hi-lo>1:
        v=(lo+hi)//2
        if worst(v)[0]*20<=den:lo=v
        else:hi=v
    peak,a,b=worst(0)
    assert worst(lo)[0]*20<=den<worst(hi)[0]*20
    return dict(estimate=str(F(threshold,n*m)),p_exact=str(F(peak,den)),p=float(F(peak,den)),least_favorable=[a,b],lower95=hi,last_rejected=str(F(worst(lo)[0],den)),first_accepted=str(F(worst(hi)[0],den)))
a=json.load(open('coffee.json'));print(json.dumps({k:calc(v) for k,v in a.items() if isinstance(v,dict)},indent=2))