"""Sharp median-only expectations and two fixed-size correlation constructions."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import comb
import csv,json

K=50
@lru_cache(None)
def hit(G,s):
    return 1-F(comb(G-s,K) if G-s>=K else 0,comb(G,K))

def signed_gram_check(G,sizes,upper):
    # Check type multiplicities in a block matrix; unit vectors and inner
    # products are explicit, hence no G-by-G positive-semidefinite solver.
    H=len(sizes);q=sizes.count(G) if upper else 0
    regular=[s for s in sizes if s!=G or not upper]
    counts=[s-q for s in regular]
    if min(counts,default=1)<1:raise ValueError('Universal degree forces larger sizes')
    extra=G-q-sum(counts)
    if extra<0:raise ValueError('Insufficient ambient genes')
    # q axes equal e0. Other groups and the filler use distinct axes e_j.
    # With q>0 their vectors are 4/5 e0 + 3/5 e_j; cross-group dot 16/25 < .7.
    # q=0 uses orthogonal clique axes. Each regular group contains one control.
    assert F(16,25)<F(7,10)<F(4,5)
    degrees=sorted([G]*q+[q+g for g in counts])
    assert degrees==sorted(sizes)
    return {'universal_controls':q,'regular_group_counts':counts,'filler':extra}

def recover_dist(G,parts,s):
    # Each part has that many controls in a disjoint s-gene clique.
    assert max(parts)<=s and len(parts)*s<=G
    dp={(0,0):1}
    for controls in parts:
        nxt=defaultdict(int)
        for (taken,rec),val in dp.items():
            for k in range(min(s,K-taken)+1):
                nxt[taken+k,rec+controls*(k!=0)]+=val*comb(s,k)
        dp=nxt
    outside=G-s*len(parts);out=defaultdict(int)
    for (taken,rec),v in dp.items():
        out[rec]+=v*comb(outside,K-taken)
    assert sum(out.values())==comb(G,K)
    return {r:F(v,comb(G,K)) for r,v in out.items()}
def pack(p):return {'numerator':p.numerator,'denominator':p.denominator,'approx':float(p)}
rows=list(csv.DictReader(open('bench_summary.csv',encoding='utf-8-sig')))
by={};classification={};overall=Counter()
for row in rows:
    group=row['cancer'];G=int(row['n_genes']);H=int(row['panel_size']);s=1+F(row['median_n_proxies']);obs=int(row['recovery_proxy'])
    if group not in by:
        if H==1:low=high=[int(s)]
        else:
            assert H%2==0 and (2*s).denominator==1
            r=H//2;S=int(2*s);candidates=[]
            for a in range(max(1,S-G),S//2+1):
                b=S-a
                lo=[1]*(r-1)+[a]+[b]*r
                hi=[a]*r+[b]+[G]*(r-1)
                candidates.append((lo,hi))
            score=lambda v:sum(hit(G,n) for n in v)
            low=min((l for l,h in candidates),key=score)
            high=max((h for l,h in candidates),key=score)
        for v in [low,high]:
            assert F(v[(H-1)//2]+v[H//2],2)==s
        lower=sum(hit(G,n) for n in low);upper=sum(hit(G,n) for n in high)
        by[group]=dict(G=G,H=H,median_size=str(s),lower=pack(lower),upper=pack(upper),lower_sizes=low,upper_sizes=high,lower_gram=signed_gram_check(G,low,False),upper_gram=signed_gram_check(G,high,True))
    rec=by[group];assert (G,H,str(s))==(rec['G'],rec['H'],rec['median_size'])
    l,u=[F(rec[k]['numerator'],rec[k]['denominator']) for k in ('lower','upper')]
    verdict='above_all' if obs>u else 'below_all' if obs<l else 'within'
    key='|'.join(row[k] for k in ('cancer','model','protocol','config'));assert key not in classification
    classification[key]={'observed':obs,'relation':verdict};overall[verdict]+=1
group=by['BRCA'];G=group['G'];s=int(group['median_size']);H=group['H'];key='BRCA|LR|RAND|ANOVA2000'
row=next(r for r in rows if '|'.join(r[k] for k in ('cancer','model','protocol','config'))==key)
assert (s,H,int(row['recovery_proxy']),int(row['recovery_top50']))==(21,12,8,4)
cases={}
for label,parts in [('disjoint',[1]*H),('shared_eight',[8,1,1,1,1])]:
    dist=recover_dist(G,parts,s)
    assert sum(r*p for r,p in dist.items())==H*hit(G,s) and dist[8]>0
    tail=sum(p for r,p in dist.items() if r>=8)
    if label=='shared_eight':assert tail==hit(G,s)
    else:assert tail<=comb(12,8)*F(comb(K,8)*s**8,comb(G,8))
    cases[label]=pack(tail)
assert cases['disjoint']['approx']<.05<cases['shared_eight']['approx']
print(json.dumps({'cohorts':by,'rows':classification,'counts':dict(overall),'overlap_witness':{'row':key,'tails':cases,'common_expectation':pack(H*hit(G,s))}},sort_keys=True))
