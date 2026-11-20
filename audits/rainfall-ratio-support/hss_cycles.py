"""Test whether rounded pairwise relative changes share a positive scalar per system."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json
def report(columns,strings):
    intervals={}
    for (a,b),s in zip(columns,strings):
        width=F(1,2*10**len(s.split('.')[1]))
        intervals[a,b]=(F(s)-width,F(s)+width)
    systems=sorted({v for p in columns for v in p})
    def check(extra):
        cap={}
        for (a,b),(lo,hi) in intervals.items():
            cap[b,a]=1+(hi+extra)/100
            cap[a,b]=1/(1+(lo-extra)/100)
        failures=[]
        for n in range(3,len(systems)+1):
            for cyc in permutations(systems,n):
                if cyc[0]!=min(cyc):continue
                prod=F(1)
                for i in range(n):prod*=cap[cyc[i-1],cyc[i]]
                if prod<1:failures.append([cyc,str(prod)])
        return failures
    lo,hi=F(0),F(1)
    if check(hi):raise ValueError('Initial bracket failed')
    failures=check(lo)
    if failures:
        for _ in range(32):
            mid=(lo+hi)/2
            if check(mid):lo=mid
            else:hi=mid
    else:hi=lo
    return dict(failing_at_printed_precision=failures,additional_percentage_points=[str(lo),str(hi)],approx=[float(lo),float(hi)])
if __name__=='__main__':
    d=json.loads(Path('hss-edges.json').read_text());print(json.dumps({k:report(d['columns'],v) for k,v in d['rows'].items()},indent=2))

