"""Compare endpoint levels with unordered, attained price extremes on the same hour."""
import csv
import hashlib
import io
import json
from collections import Counter, defaultdict
from datetime import datetime, timedelta
from fractions import Fraction as Q
from itertools import product
from urllib.request import Request, urlopen

from endpoints import bounds, classify, direct_lp

URL = 'https://aemo.com.au/aemo/data/nem/priceanddemand/PRICE_AND_DEMAND_202503_NSW1.csv'
DIGEST = 'bc5589d85400e2ce9dcbf93232ca17676280f3b0d6369a208c37efb923a04986'


def variation(p):
    return sum(abs(a-b) for a,b in zip(p,p[1:]))


def early_margin(p):
    half=len(p)//2
    return (sum(p[:half])-sum(p[half:]))/len(p)


def sharp_radius(total,low,high,size):
    return min(total-size*low, size*high-total)/size


def extremizers(total,low,high,size):
    excess=total-size*low
    desc=[]
    for _ in range(size):
        add=min(excess,high-low)
        desc.append(low+add)
        excess-=add
    assert excess==0 and min(desc)==low and max(desc)==high
    return desc,desc[::-1]


def test_tiny():
    groups=defaultdict(list)
    for v in product(range(4), repeat=6):
        p=list(map(Q,v))
        l,h=min(p),max(p)
        tv=variation(p)
        groups[(l,h,sum(p),tv)].append(early_margin(p))
        if l==h:
            continue
        orientation=1 if p.index(h)<p.index(l) else -1
        floor=(h-l-3*(tv-(h-l)))/6
        assert orientation*early_margin(p)>=floor
    for (l,h,total,cap),values in groups.items():
        r=sharp_radius(total,l,h,6)
        extrema=[v for (l2,h2,t2,used),vs in groups.items() if (l,h,total)==(l2,h2,t2) and used<=cap for v in vs]
        assert max(extrema)==r and min(extrema)==-r
        if cap==h-l and h>l:
            assert all(abs(v)>=(h-l)/6 for v in values)
    return len(groups)


def study():
    checked=test_tiny()
    with urlopen(Request(URL,headers={'User-Agent':'Mozilla/5.0 (research replay)'}),timeout=60) as f:
        raw=f.read()
    assert hashlib.sha256(raw).hexdigest()==DIGEST
    rows=list(csv.DictReader(io.StringIO(raw.decode('utf-8-sig'))))
    start=datetime(2025,3,1)
    assert len(rows)==744*12
    for i,r in enumerate(rows,1):
        assert (r['REGION'],r['PERIODTYPE'])==('NSW1','TRADE')
        assert datetime.strptime(r['SETTLEMENTDATE'],'%Y/%m/%d %H:%M:%S')==start+timedelta(minutes=5*i)
    d=[Q(1,12)]*6+[Q(-1,12)]*6
    counts=Counter();results=[]
    for hour in range(744):
        p=[Q(r['RRP']) for r in rows[hour*12:hour*12+12]]
        total=sum(p);low,high=min(p),max(p);spread=high-low;tv=variation(p)
        radius=sharp_radius(total,low,high,12);actual=early_margin(p)
        high_path,low_path=extremizers(total,low,high,12)
        for path,expected in ((high_path,radius),(low_path,-radius)):
            assert sum(path)==total and variation(path)<=tv and early_margin(path)==expected
        (lo,_),(hi,_)=bounds(p[0],p[-1],total/12,tv,d)
        solver=direct_lp(p[0],p[-1],total/12,tv,d)
        assert all(abs(float(v)-x)<1e-7*max(1,abs(float(v))) for v,x in zip((lo,hi),solver))
        assert lo<=actual<=hi and abs(actual)<=radius
        kind=classify(lo,hi)
        counts['A_'+kind]+=1
        counts['B_'+classify(-radius,radius)]+=1
        counts['width_'+('A_smaller' if hi-lo<2*radius else 'B_smaller' if hi-lo>2*radius else 'equal')]+=1
        if tv==spread and spread>0:
            interior=(total-low-high)/10
            monotone=[low]+[interior]*10+[high]
            assert variation(monotone)==tv and early_margin(monotone)==-spread/12
            counts['nonflat_minimal_variation']+=1
        floor=(spread-6*(tv-spread))/12
        oriented=None
        if spread>0:
            oriented=1 if p.index(high)<p.index(low) else -1
            assert oriented*actual>=floor
        if floor>0:
            counts['order_bit_certified']+=1
            counts['order_bit_early' if oriented==1 else 'order_bit_late']+=1
        results.append(dict(hour=(start+timedelta(hours=hour)).isoformat(),realized=actual,
                            mean=total/12,variation=tv,minimum=low,maximum=high,
                            endpoint_extrema=[lo,hi],unordered_extrema=[-radius,radius],
                            positive_witness=high_path,negative_witness=low_path,
                            certified_order_margin_floor=max(0,floor),first_extreme_orientation=oriented))
    return dict(url=URL,digest=DIGEST,intervals=len(rows),counts=dict(sorted(counts.items())),
                tiny_vectors=4096,tiny_summary_classes=checked,lp_checks=1488,hours=results)


if __name__=='__main__':
    print(json.dumps(study(),default=str))
