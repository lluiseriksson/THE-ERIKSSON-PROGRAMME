from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import comb
import csv,json
def rows(name):
    with open(name,encoding='utf-8-sig',newline='') as f:return list(csv.DictReader(f))
kept=rows('lista_EID_corpus_576.csv');excluded=rows('registro_exclusiones_137.csv');pilot=rows('muestra_relevancia_30.csv')
assert len({r['EID'] for r in kept+excluded})==713 and len(pilot)==30
def choose(n,k):return comb(n,k) if 0<=k<=n else 0
def period(last):
    pool=[r for r in kept+excluded if int(r['Year'])<=last]
    c3=[r for r in excluded if int(r['Year'])<=last and r['criterio'].startswith('C3')]
    fixed=[r for r in kept if int(r['Year'])<=last]
    sample=[r for r in pilot if int(r['anio'])<=last]
    def recent(group,col):return sum(int(r[col])>=2021 for r in group)
    a=recent(fixed,'Year');z=len(fixed)-a;e=recent(c3,'Year');f=len(c3)-e
    N=len(pool);n=len(sample);nR=recent(pool,'Year');nO=N-nR
    counts=Counter((int(r['anio'])>=2021,r['relevante'].strip().casefold()) for r in sample)
    assert {r['relevante'].strip().casefold() for r in sample}=={'si','no'}
    obs=counts[True,'si']-counts[False,'si']
    den=comb(N,n)
    @lru_cache(None)
    def tail(A,B):
        return sum(choose(A,i)*choose(B,j)*choose(N-A-B,n-i-j) for i in range(n+1) for j in range(min(n-i,i-obs)+1))
    def worst(d):
        candidates=[(tail(A,max(0,A-d)),A,max(0,A-d)) for A in range(nR+1) if max(0,A-d)<=nO];return max(candidates) if candidates else (0,None,None)
    top,A,B=worst(0)
    lo,hi=-nO-1,nR
    while hi-lo>1:
        mid=(lo+hi)//2
        if 20*worst(mid)[0]<=den:lo=mid
        else:hi=mid
    return dict(last_year=last,kept=[a,z],c3=[e,f],sharp_min=str(F(a,a+z+f)),sharp_max=str(F(a+e,a+e+z)),population=[nR,nO],sample=n,pilot_recent=[counts[True,'si'],counts[True,'no']],pilot_early=[counts[False,'si'],counts[False,'no']],score=obs,p_exact=str(F(top,den)),p=float(F(top,den)),null_witness=[A,B],lower95_net_recent=hi,last_rejected=str(F(worst(lo)[0],den)),first_accepted=str(F(worst(hi)[0],den)))
proof_checks=0
from itertools import combinations
for A in range(8):
 for B in range(8-A):
    labels=[1]*A+[-1]*B+[0]*(7-A-B)
    for obs in range(-3,4):
        numerator=sum(choose(A,i)*choose(B,j)*choose(7-A-B,3-i-j) for i in range(4) for j in range(min(3-i,i-obs)+1))
        if numerator!=sum(sum(s)>=obs for s in combinations(labels,3)):raise ValueError('Tail mismatch')
        proof_checks+=1
print(json.dumps(dict(through_snapshot=period(2026),through_last_complete_year=period(2025),small_tests=proof_checks),indent=2))