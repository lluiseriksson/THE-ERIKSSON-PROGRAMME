"""Exact completion thresholds for the 19 November registry snapshot; Python standard library."""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations,product
from collections import Counter
import csv,json,calendar,datetime

def require(ok,message):
    if not ok:raise ValueError(message)

def readrows(name):
    with (Path(__file__).parent/name).open(encoding='utf-8-sig',newline='') as f:return list(csv.DictReader(f))

def ceiling(x):
    return -((-x.numerator)//x.denominator)

def additions(h,n,t,strict=False):
    if t==1:return None if strict or h<n else 0
    x=(t*n-h)/(1-t)
    return max(0,x.numerator//x.denominator+1 if strict else ceiling(x))

def prefix_check(demand,caps):
    used=0
    for m,x in sorted(demand.items()):
        used+=x
        if used>caps[m]:return False,m
    return True,None

def main():
    pending=readrows('p90_by_month.csv')
    cells={};omitted=[];date=datetime.date(2026,11,19)
    for r in readrows('s2_qc_to_post_by_qc_month.csv'):
        m=r['qc_month']
        if not r['share_over_30'] or len(m)!=7:omitted.append(m);continue
        y,mo=map(int,m.split('-'));last=datetime.date(y,mo,calendar.monthrange(y,mo)[1])
        if (date-last).days<30:omitted.append(m);continue
        n=int(r['units']);reported=F(r['share_over_30'])
        hs=[h for h in range(n+1) if abs(F(h,n)-reported)<=F(1,200000)]
        require(len(hs)==1,m);cells[m]=(hs[0],n)
    pool={r['period']:int(r['pending']) for r in pending}
    restricted={r['period']:int(r['pending'])-(int(r['n_all'])-int(r['n_excl_unrelease_pending'])) for r in pending}
    require(all(0<=restricted[m]<=pool[m] for m in pool),'restricted pool')
    reports={}
    for label,eligible in [('all',pool),('excluding_unreleased',restricted)]:
        caps={m:sum(v for s,v in eligible.items() if s<=m) for m in cells}
        pairs=[];counts=Counter()
        for a,b in combinations(cells,2):
            h,n=cells[a];g,z=cells[b]
            if F(h,n)==F(g,z):
                counts['observed_tie']+=1;continue
            lo,hi=(a,b) if F(h,n)<F(g,z) else (b,a)
            H,N=cells[lo];t=F(*cells[hi]);x=additions(H,N,t,True);y=additions(H,N,t)
            upper=F(H+caps[lo],N+caps[lo])
            kind='reversible' if upper>t else 'tie_only' if upper==t else 'strictly_preserved'
            require((x is not None and x<=caps[lo])==(kind=='reversible'),'ordering disagreement')
            counts[kind]+=1
            pairs.append(dict(lower=lo,higher=hi,minimum_tie_or_more=y,minimum_strict_reversal=x,eligible=caps[lo],status=kind))
        base=[m for m in cells if '2021-10'<=m<='2024-12']
        zero=[m for m in cells if '2025-02'<=m<='2026-04']
        require(len(base)==39 and len(zero)==15 and not any(cells[m][0] for m in zero),'period definition')
        bh=sum(cells[m][0] for m in base);bn=sum(cells[m][1] for m in base);ref=F(bh,bn)
        minref=min(F(*cells[m]) for m in base)
        scenarios={}
        for key,t in [('baseline_pooled',ref),('lowest_baseline_month',minref)]:
            ds={m:additions(*cells[m],t) for m in zero};ok,cut=prefix_check(ds,caps)
            total_n=sum(cells[m][1] for m in zero)
            scenarios[key]=dict(reference=str(t),per_month=ds,total=sum(ds.values()),feasible=ok,first_binding_failure=cut,pooled_only=additions(0,total_n,t))
        # Every attainable common minimum equals one month's attained share.
        candidates=sorted({F(x,cells[m][1]+x) for m in zero for x in range(caps[m]+1)})
        def demands(t):return {m:additions(*cells[m],t) for m in zero}
        low=0;high=len(candidates)
        while high-low>1:
            mid=(low+high)//2
            if prefix_check(demands(candidates[mid]),caps)[0]:low=mid
            else:high=mid
        best=candidates[low];ds=demands(best)
        # Infinitesimal increase: each month must strictly exceed this exact level.
        strict={m:additions(*cells[m],best,True) for m in zero}
        ok,blocking=prefix_check(strict,caps)
        require(not ok and prefix_check(ds,caps)[0],'extremal prefix')
        reports[label]=dict(pool=sum(eligible.values()),counts=dict(counts),pairs=pairs,baseline=[bh,bn],zero_units=sum(cells[m][1] for m in zero),scenarios=scenarios,maximin=dict(value=str(best),approx=float(best),demands=ds,total=sum(ds.values()),capacity_at_block=caps[blocking],first_block=blocking,strict_demand_at_block=sum(x for m,x in strict.items() if m<=blocking)))
    # Independent miniature assignment oracle: each unit goes to an eligible month or outside.
    mini=0
    for s in product(range(3),repeat=3):
        caps={i:sum(j<=i for j in s) for i in range(3)}
        attainable={tuple(p.count(i) for i in range(3)) for p in product(range(4),repeat=3) if all(y>=x for x,y in zip(s,p))}
        for ds in product(range(4),repeat=3):
            require(prefix_check(dict(enumerate(ds)),caps)[0]==(ds in attainable),'miniature assignment')
            mini+=1
    print(json.dumps(dict(snapshot=date.isoformat(),months=len(cells),omitted=omitted,recovered=cells,mini_checks=mini,reports=reports)))
if __name__=='__main__':main()