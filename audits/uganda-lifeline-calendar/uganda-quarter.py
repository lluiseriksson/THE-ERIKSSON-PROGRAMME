"""Q4 tariff memory for synthetic seasonal allocations from two archived load shapes."""
from fractions import Fraction as Q
from itertools import combinations
from collections import defaultdict,Counter
from pathlib import Path
from calendar import monthrange
from zipfile import ZipFile
import json
def check(test,msg):
    if not test:raise ValueError(msg)
def calc(raw):
    with ZipFile(raw) as z:
        daily=[]
        for n in (3,4,5):
            p,=[f for f in z.namelist() if f.endswith(f'/load_{n}kWh_day_local.csv')]
            data=[Q(x) for x in z.read(p).decode().splitlines() if x.strip()]
            check(len(data)==8760 and data==data[:24]*365,'Load not repeated daily')
            daily.append(sum(data[:24]))
    days=[monthrange(2026,m)[1] for m in range(1,13)]
    def energy(x):
        return min(x,80)*Q('779.4')+max(0,min(x,150)-80)*412+max(0,x-150)*Q('779.4')
    def bill(x,eligible):return energy(x)-(Q('779.4')-250)*min(15,x)*int(eligible)
    def summer(m):return [sum(m[i-6:i]) for i in [9,10,11]]
    def get(m):
        # Independent cut computation: all three prior averages against 100 kWh.
        prior=summer(m);eligible=[p<=600 for p in prior]
        base=sum(energy(x) for x in m[9:]);saved=sum((Q('779.4')-250)*min(15,x)*int(k) for x,k in zip(m[9:],eligible))
        charge=sum(bill(m[i],sum(m[i-6:i])/6<=100) for i in [9,10,11])
        check(charge==base-saved,'Rule mismatch')
        return charge,prior,eligible
    orig={}
    for load,q in zip([3,4,5],daily):
        m=[q*n for n in days];charge,pre,elig=get(m)
        flat=sum(m)/12
        orig[load]=dict(daily=str(q),disaggregated_q4=str(charge),flat_three_bills=str(3*bill(flat,flat<=100)),difference=str(charge-3*bill(flat,flat<=100)),eligibility=elig)
    grouped=defaultdict(list);counts=Counter()
    for high in combinations(range(12),6):
        m=[days[i]*daily[2 if i in high else 0] for i in range(12)]
        charge,pre,elig=get(m)
        # Hold fixed even the entire multiset of monthly usage, and Q4 in order.
        key=(tuple(sorted(m)),tuple(m[9:]))
        grouped[key].append((charge,high,pre,elig));counts[sum(elig)]+=1
    extrema=[]
    for key,vs in grouped.items():
        lo,hi=min(vs),max(vs);delta=hi[0]-lo[0];extrema.append((delta,key,lo,hi,len(vs)))
    delta,key,lo,hi,size=max(extrema)
    def render(entry):
        charge,high,pre,elig=entry
        return dict(charge=str(charge),high_months=[i+1 for i in high],previous_six_month_totals=list(map(str,pre)),eligible=elig)
    # Only three bills and the first fifteen units can change in each.
    check(delta<=3*15*(Q('779.4')-250),'Exceeds universal cap')
    return dict(original_fixed_shapes=orig,annual_patterns=sum(counts.values()),matched_groups=len(grouped),number_nonzero_spread=sum(x[0]>0 for x in extrema),eligible_months_distribution=dict(counts),maximum_spread_UGX=str(delta),ceiling_UGX=str(3*15*(Q('779.4')-250)),q4_monthly_kWh=list(map(str,key[1])),annual_month_multiset=list(map(str,key[0])),group_size=size,low_bill_witness=render(lo),high_bill_witness=render(hi))
if __name__=='__main__':print(json.dumps(calc('source.zip'),sort_keys=True,indent=2))