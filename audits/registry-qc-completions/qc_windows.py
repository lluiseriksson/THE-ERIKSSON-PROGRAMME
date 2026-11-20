"""Timing requirements for pending-record explanations. Integer months and calendar days."""
from fractions import Fraction as F
from datetime import date,timedelta
from calendar import monthrange
from itertools import product
from collections import Counter
from qc_frontier import readrows,additions,require
import json

def num(m):
    y,v=map(int,m.split('-'));return 12*y+v-1

def text(t):return f'{t//12:04d}-{t%12+1:02d}'

def feasible(pool,demands,W):
    supply=pool.copy();moves=[]
    for m,n in sorted(demands.items()):
        for s in sorted(s for s in supply if m-W<=s<=m):
            take=min(supply[s],n)
            if take:
                moves.append((s,m,take));supply[s]-=take;n-=take
            if not n:break
        if n:return None
    return [(text(s),text(m),v) for s,m,v in moves]

def main():
    p=readrows('p90_by_month.csv');qc=readrows('s2_qc_to_post_by_qc_month.csv')
    zero={num(r['qc_month']):int(r['units']) for r in qc if '2025-02'<=r['qc_month']<='2026-04'}
    old=[(int(r['units']),F(r['share_over_30'])) for r in qc if '2021-10'<=r['qc_month']<='2024-12']
    hs=[round(n*h) for n,h in old]
    refs={'pooled':F(sum(hs),sum(n for n,h in old)),'minimum':min(F(x,n) for x,(n,h) in zip(hs,old))}
    post=date(2026,11,20)
    delays={m:(post-date(m//12,m%12+1,monthrange(m//12,m%12+1)[1])).days for m in zero}
    res={};mini=0
    for starts in product(range(3),repeat=3):
        pool=dict(Counter(starts))
        for W in [0,1,2]:
            counts={tuple(xs.count(m) for m in range(3)) for xs in product(range(4),repeat=3) if all(m==3 or s<=m<=s+W for s,m in zip(starts,xs))}
            for ds in product(range(4),repeat=3):
                require((feasible(pool,dict(enumerate(ds)),W) is not None)==(ds in counts),'window oracle');mini+=1
    for mode in ['all','excluding_unreleased']:
        pool={num(r['period']):int(r['pending'])-(int(r['n_all'])-int(r['n_excl_unrelease_pending']) if mode=='excluding_unreleased' else 0) for r in p}
        for name,r in refs.items():
            ds={m:additions(0,n,r) for m,n in zero.items()}
            width=next(W for W in range(150) if feasible(pool,ds,W) is not None)
            moves=feasible(pool,ds,width)
            def shortages(W):
                intervals=[]
                for a in sorted(ds):
                    for b in sorted(m for m in ds if m>=a):
                        demand=sum(v for m,v in ds.items() if a<=m<=b)
                        eligible=sum(v for s,v in pool.items() if a-W<=s<=b)
                        if demand>eligible:intervals.append((demand-eligible,text(a),text(b),demand,eligible))
                return max(intervals) if intervals else None
            block=shortages(width-1) if width else None
            require(width==0 or block is not None,'missing lower certificate')
            res[mode+':'+name]=dict(minimum_submission_to_qc_months=width,allocation=moves,one_month_less_deficit=block,minimum_required_pending=sum(ds.values()),minimum_qc_to_post_day_cap=max(delays.values()),minimum_counts_over_horizon={str(t):sum(ds[m] for m in ds if delays[m]>t) for t in [90,180,365,540,600]},reference=str(r))
    print(json.dumps(dict(results=res,mini_checks=mini,earliest_post=post.isoformat(),day_costs={text(m):v for m,v in delays.items()})))
if __name__=='__main__':main()