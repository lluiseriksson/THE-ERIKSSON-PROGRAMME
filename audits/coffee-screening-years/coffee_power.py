"""Least detectable excess, using exact finite-population size and power comparisons."""
from math import comb
from functools import lru_cache
from fractions import Fraction as F
import json
import numpy as np
N,M=424,259
def choose(n,k):return comb(n,k) if 0<=k<=n else 0
def solve(n):
    m=60-n;den=comb(N,n)*comb(M,m)
    pm=[[choose(a,i)*choose(N-a,n-i) for i in range(n+1)] for a in range(N+1)]
    cum=[]
    for b in range(M+1):
        xs=[0]
        for j in range(m+1):xs.append(xs[-1]+choose(b,j)*choose(M-b,m-j))
        cum.append(xs)
    fa=np.array(pm,dtype=float)/float(comb(N,n));fb=np.array(cum,dtype=float)/float(comb(M,m))
    scores=sorted({N*i*m-M*j*n for i in range(n+1) for j in range(m+1)});scores.append(scores[-1]+1)
    @lru_cache(None)
    def calc(idx,delta,exact):
        limits=[max(0,min(m+1,1+(N*i*m-scores[idx])//(M*n))) for i in range(n+1)]
        if delta==0:
            a=range(min(N,M+5)+1);b=[max(0,k-5) for k in a]
        else:
            b=range(min(M,N-delta-5)+1);a=[k+delta+5 for k in b]
        if not exact:
            arr=(fa[list(a)]*fb[np.ix_(list(b),limits)]).sum(axis=1)
            return float(max(arr) if delta==0 else min(arr))
        pairs=[(sum(u*cum[B][v] for u,v in zip(pm[A],limits)),A,B) for A,B in zip(a,b)]
        return (max if delta==0 else min)(pairs)
    def good(idx,d):
        p=calc(idx,d,False);bound=.05 if not d else .80
        if abs(p-bound)>1e-10:return p<bound if not d else p>bound
        v=calc(idx,d,True)[0]
        return (20*v<=den) if not d else (5*v>=4*den)
    lo,hi=-1,len(scores)-1
    while hi-lo>1:
        k=(lo+hi)//2
        if good(k,0):hi=k
        else:lo=k
    critical=hi
    def compact(idx,d):
        v,a,b=calc(idx,d,True);return {'numerator':str(v),'A':a,'B':b}
    size=compact(critical,0);prev=compact(critical-1,0)
    if not int(size['numerator'])*20<=den<int(prev['numerator'])*20:raise ValueError('Critical score mismatch')
    lo,hi=0,N-5
    if not good(critical,hi):
        fail=compact(critical,hi)
        if int(fail['numerator'])*5>=4*den:raise ValueError('Worst case')
        return dict(n=n,m=m,score=scores[critical],den=str(den),size=size,previous=prev,delta=None,power_at_max=fail)
    while hi-lo>1:
        d=(lo+hi)//2
        if good(critical,d):hi=d
        else:lo=d
    power=compact(critical,hi);before=compact(critical,hi-1)
    if not int(before['numerator'])*5<4*den<=int(power['numerator'])*5:raise ValueError('Power boundary mismatch')
    return dict(n=n,m=m,score=scores[critical],den=str(den),size=size,previous=prev,delta=hi,power=power,one_less=before)
if __name__=='__main__':
    rows=[solve(n) for n in range(1,60)]
    best=min(r['delta'] for r in rows if r['delta'] is not None)
    print(json.dumps(dict(extra=60,target_power='4/5',size='1/20',recent_unknown=N,earlier_unknown=M,known_difference=-5,best=best,optima=[r['n'] for r in rows if r['delta']==best],rows=rows),indent=2))