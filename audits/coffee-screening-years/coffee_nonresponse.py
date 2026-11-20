"""Least detectable excess, using exact finite-population size and power comparisons."""
from math import comb
from functools import lru_cache
from fractions import Fraction as F
import json
import numpy as np
N,M=424,259
def choose(n,k):return comb(n,k) if 0<=k<=n else 0
def limits_for(N,M,n,m,cut,k):
    limits=[]
    for i in range(n+1):
        last=m
        for a in range(k+1):
            h=(N*m*max(i-a,0)-cut)//(M*n)
            if h<m:last=min(last,h-(k-a))
        limits.append(max(0,last+1))
    return limits

def validate_small():
    from itertools import combinations
    checks=0
    for n,m in [(2,3),(3,2),(1,4)]:
        N,M=7,5
        for k in range(4):
            for cut in sorted({N*m*i-M*n*j for i in range(n+1) for j in range(m+1)}):
                lim=limits_for(N,M,n,m,cut,k)
                for i in range(n+1):
                    for j in range(m+1):
                        impacts=[N*m]*i+[0]*(n-i)+[0]*j+[M*n]*(m-j)
                        masks=(sel for z in range(min(k,n+m)+1) for sel in combinations(impacts,z))
                        worst=N*m*i-M*n*j-max(sum(sel) for sel in masks)
                        if (worst>=cut)!=(j<lim[i]):raise ValueError('Suppression formula')
                        checks+=1
    return checks

def solve(n,missing_budget):
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
        limits=limits_for(N,M,n,m,scores[idx],missing_budget if delta else 0)
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
    out={'small_checks':validate_small(),'levels':{}}
    for k in range(4):
        rows=[solve(n,k) for n in range(1,60)]
        best=min(r['delta'] for r in rows if r['delta'] is not None)
        out['levels'][k]=dict(best=best,optima=[r['n'] for r in rows if r['delta']==best],rows=rows)
    baseline=json.load(open('power.json'))
    if out['levels'][0]['rows']!=baseline['rows']:raise ValueError('Complete-label reference failed')
    print(json.dumps(out,indent=2))