"""Verify the suffix-order theorem against every binary calendar in the archived load panel."""
from fractions import Fraction as Q
from itertools import product
from calendar import monthrange
from collections import defaultdict,Counter
import json,zipfile
def need(x,msg):
    if not x:raise ValueError(msg)
def panel():
    with zipfile.ZipFile('source.zip') as z:
        q=[]
        for n in (3,5):
            f,=[p for p in z.namelist() if p.endswith(f'/load_{n}kWh_day_local.csv')]
            v=[Q(s) for s in z.read(f).decode().splitlines()]
            need(v==v[:24]*365,'Stationary day violated');q.append(sum(v[:24]))
    days=tuple(monthrange(2026,j)[1] for j in range(1,13))
    def usage(mask):return tuple(d*q[i] for d,i in zip(days,mask))
    def flags(mask):
        x=usage(mask);return tuple(sum(x[j-6:j])<=600 for j in (9,10,11))
    def ordered(mask,high_first):
        out=list(mask)
        for d in set(days[:9]):
            ix=[j for j in range(9) if days[j]==d]
            for j,i in zip(ix,sorted([mask[k] for k in ix],reverse=high_first)):out[j]=i
        return tuple(out)
    groups=defaultdict(list)
    for mask in product((0,1),repeat=12):
        x=usage(mask);groups[(tuple(sorted(x)),x[9:])].append((flags(mask),mask))
    hist=Counter();six=Counter();examples={};per_n={}
    for k,entries in groups.items():
        mask=entries[0][1];n=sum(mask);low=ordered(mask,True);high=ordered(mask,False)
        good,bad=flags(low),flags(high)
        need(all(all(a<=b<=c for a,b,c in zip(bad,f,good)) for f,_ in entries),'Failed coordinate dominance')
        need({low,high}<={m for f,m in entries},'Invalid achievable calendar')
        spread=sum(good)-sum(bad);hist[spread]+=1
        if n==6:six[spread]+=1
        per_n[str(n)]=max(per_n.get(str(n),0),spread)
        if str(spread) not in examples:
            examples[str(spread)]=dict(high_months_cheapest=[j+1 for j,i in enumerate(low) if i],high_months_dearest=[j+1 for j,i in enumerate(high) if i],eligibility_cheapest=good,eligibility_dearest=bad,q4=list(map(str,k[1])),histogram=list(map(str,k[0])))
    return dict(calendars=2**12,groups=len(groups),by_spread_in_discount_months=dict(hist),six_high_groups=dict(six),max_months_by_high_count=per_n,witnesses=examples,discount_per_month_UGX='7941')
if __name__=='__main__':print(json.dumps(panel(),sort_keys=True,indent=2))