"""Verify integer margins for selective FinRank corruption, without extrapolating to deployments."""
import json
from collections import defaultdict
from itertools import combinations
def feasible(n,clean,exclusive,neither,k):
    both=n-exclusive-neither
    out={}
    for x in range(max(0,k-(n-exclusive)),min(exclusive,k)+1):
        lo=max(0,clean-k)+max(0,k-x-both)
        hi=min(clean,n-k)+min(neither,k-x)
        out[x]=(lo,hi)
    return out
def brute(n,clean,exclusive,neither,k):
    ids=set(range(n))
    extra=set(range(exclusive))
    missed=set(range(exclusive,exclusive+neither))
    out=defaultdict(set)
    for C in combinations(ids,clean):
        for chosen in combinations(ids,k):
            S=set(chosen);h=len(set(C)-S);x=len(extra&S);out[x].add(h+len(missed&S))
    return out
def main():
    grids=0
    for n in range(1,7):
        for clean in range(n+1):
            for x in range(n+1):
                for y in range(n-x+1):
                    for k in range(n+1):
                        grid=feasible(n,clean,x,y,k)
                        if {j:set(range(lo,hi+1)) for j,(lo,hi) in grid.items()}!=brute(n,clean,x,y,k):raise ValueError((n,clean,x,y,k))
                        grids+=1
    curves={k:feasible(60,30,25,14,k) for k in range(61)}
    any_gain=min(k for k,v in curves.items() if min(v)>0)
    clean_below=min(k for k,v in curves.items() if max(hi for lo,hi in v.values())<30)
    if (any_gain,clean_below)!=(36,45):raise ValueError('Mistral threshold mismatch')
    # Conditional on the R1 correct corrupted majority belonging or not to the exclusive flags.
    counts=[40-g+1 for g in [8,9]]
    print(json.dumps(dict(grids=grids,mistral_guaranteed_gain=any_gain,mistral_strict_below_clean=clean_below,
        mistral_k30=curves[30],r1_strict_thresholds=counts),sort_keys=True))
if __name__=='__main__':main()