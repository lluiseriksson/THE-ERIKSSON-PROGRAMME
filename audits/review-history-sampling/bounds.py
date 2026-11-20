from fractions import Fraction as F
from math import comb
from collections import Counter

def bounds(coverage):
    profile=Counter();actual_editors=0
    for n,y,e,c in coverage["counts"]:
        profile[n,y]+=c;actual_editors+=e*c
    base=F(0);forced=0;gains=[]
    for (n,y),freq in profile.items():
        if y in (0,n):
            forced+=freq*(y==n)
            continue
        uniform=1-F(comb(n-y,2),comb(n,2))
        review=F(y,n-1)
        base+=freq*(review-uniform)
        gains.extend([(1-review,n,y)]*freq)
    if not 0<=actual_editors-forced<=len(gains):raise ValueError("count out of range")
    m=sum(profile.values());ordered=sorted(gains)
    # Independently enumerate attainable minima and maxima at each cardinality.
    dp={0:(F(0),F(0))}
    for gain,n,y in gains:
        nxt=dp.copy()
        for k,(a,b) in dp.items():
            lo,hi=nxt.get(k+1,(a+gain,b+gain))
            nxt[k+1]=min(lo,a+gain),max(hi,b+gain)
        dp=nxt
    intervals={}
    for k in range(len(gains)+1):
        small=ordered[:k];large=list(reversed(ordered))[:k]
        lo=sum((v for v,n,y in small),F(0));hi=sum((v for v,n,y in large),F(0))
        if dp[k]!=(lo,hi):raise ValueError("knapsack readback")
        intervals[k+forced]=[(base+lo)/m,(base+hi)/m]
    measured=F(coverage["curves"]["2"]["difference"])
    lower,upper=intervals[actual_editors]
    if not lower<=measured<=upper:raise ValueError("outside margins")
    return dict(article_count=m,actual_editors=actual_editors,forced=forced,observed=measured,actual_bounds=[lower,upper],
                by_editor_count=intervals,
                first_possible_win=next((k for k,(a,b) in intervals.items() if b>0),None),
                first_necessary_win=next((k for k,(a,b) in intervals.items() if a>0),None),
                free_profile_gains=[[n,y,v] for v,n,y in ordered],dp_cardinalities=len(dp))
