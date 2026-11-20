"""Exact worst case with one missing second-sample rating, frame 127, sample size 32."""
from itertools import combinations
import json
N, n, offset, threshold = 127, 32, 48, 62
full = (1 << N) - 1
def sample(s):
    return sum(1 << ((s+j*N)//n) for j in range(n))
a = [sample(s) for s in range(N)]
b = [a[(s+offset)%N] for s in range(N)]
c = full ^ (a[0] | b[0])
def positions(mask):
    return [j for j in range(N) if mask >> j & 1]
def candidates():
    for i in positions(c):
        yield c ^ (1 << i)
    for i,j in combinations(positions(c),2):
        remaining = c ^ (1 << i) ^ (1 << j)
        for k in positions(b[0]):
            yield remaining | (1 << k)
def misses(p):
    return [s for s in range(N) if (p & a[s])==0 and (p & b[s]).bit_count()<=1]
worst, checked, histogram = 0, 0, {}
for p in candidates():
    phases=misses(p)
    if p.bit_count()!=threshold or 0 not in phases:raise ValueError('bad phase-zero candidate')
    checked+=1; count=len(phases);histogram[count]=histogram.get(count,0)+1
    if count>worst:
        worst=count;witness=positions(p);attained=phases
if checked!=62559:raise ValueError(checked)
# A second, shift-independent certificate: implications across ALL offsets.
lower_by_offset=[]
for delta in range(N):
    pool = full ^ (a[0] | a[delta] | a[1])
    if pool.bit_count()<threshold:raise ValueError(delta)
    p=sum(1<<i for i in positions(pool)[:threshold])
    if p & a[1] or (p & a[(delta+1)%N]).bit_count()>1:raise ValueError('failed lower bound')
    lower_by_offset.append(delta)
print(json.dumps(dict(worst=worst,phases=attained,witness=witness,checked=checked,
    counts_by_number_of_undetected_phases=histogram,offset=offset,N=N,n=n,positive_count=threshold,
    lower_bound_for_all_offsets=2,number_of_offsets_checked=len(lower_by_offset)),indent=2))