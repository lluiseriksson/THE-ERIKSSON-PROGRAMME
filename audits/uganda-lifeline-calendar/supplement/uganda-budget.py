"""Sharp bills under bounded chronological reassignment of energy, Q4 2026."""
import itertools,json,zipfile
from fractions import Fraction as Q
from calendar import monthrange
def need(c):
    if not c:raise ValueError('Transfer witness mismatch')
def redistribute(x,lo,hi,b,up):
    if not up:return redistribute(x[::-1],lo[::-1],hi[::-1],b,True)[::-1]
    v=list(x);i=0;j=len(v)-1
    while i<j and b:
        a=min(v[i]-lo[i],hi[j]-v[j],b);v[i]-=a;v[j]+=a;b-=a
        if v[i]==lo[i]:i+=1
        if v[j]==hi[j]:j-=1
    return tuple(v)
def suffix(x,k):return sum(x[k:])
def pair(x,lo,hi,b):
    low=redistribute(x,lo,hi,b,False);high=redistribute(x,lo,hi,b,True)
    for v in [low,high]:
        need(sum(x)==sum(v) and sum(abs(a-z) for a,z in zip(v,x))<=2*b)
        need(all(l<=a<=h for a,l,h in zip(v,lo,hi)))
    for k in range(len(x)+1):
        upper=min(b,sum(h-a for h,a in zip(hi[k:],x[k:])),sum(a-l for a,l in zip(x[:k],lo[:k])))
        lower=min(b,sum(a-l for a,l in zip(x[k:],lo[k:])),sum(h-a for h,a in zip(hi[:k],x[:k])))
        need(suffix(high,k)==suffix(x,k)+upper and suffix(low,k)==suffix(x,k)-lower)
    return low,high
def small():
    total=0
    for upper in itertools.product((1,2),repeat=4):
        lo=(0,)*4;hist=list(itertools.product(*(range(h+1) for h in upper)))
        for x in hist:
            for b in range(4):
                low,high=pair(x,lo,upper,b)
                for v in hist:
                    if sum(v)!=sum(x) or sum(abs(a-z) for a,z in zip(v,x))>2*b:continue
                    total+=1
                    need(all(suffix(low,k)<=suffix(v,k)<=suffix(high,k) for k in range(5)))
    return total
def app():
    with zipfile.ZipFile('source.zip') as z:
        rates=[sum(map(Q,z.read(next(p for p in z.namelist() if p.endswith(f'/load_{n}kWh_day_local.csv'))).decode().splitlines()[:24])) for n in (3,5)]
    d=[monthrange(2026,m)[1] for m in range(1,13)]
    lo=tuple(rates[0]*n for n in d);hi=tuple(rates[1]*n for n in d)
    result={}
    for label,months in [('January',[1]),('August',[8]),('six_favorable',[1,2,3,4,11,12]),('six_dearer',[2,7,8,9,11,12])]:
        x=tuple(h if j+1 in months else l for j,(l,h) in enumerate(zip(lo,hi)));p=x[:9];fixed=x[9:]
        def totals(v):return tuple(sum((v+fixed)[j-6:j]) for j in [9,10,11])
        def flags(v):return [t<=600 for t in totals(v)]
        # The archived grid is in 0.0001 kWh; strict inequality becomes >=600.0001.
        res={}
        for up in [False,True]:
            key='all_ineligible' if up else 'all_eligible'
            b=max([Q(0)]+[(Q('600.0001')-a if up else a-600) for a in totals(p)])
            l,h=pair(p,lo[:9],hi[:9],b);v=h if up else l
            ok=all(k==(not up) for k in flags(v))
            if not ok:
                a,z=pair(p,lo[:9],hi[:9],sum(p));need(not all(k==(not up) for k in flags(z if up else a)))
                res[key]=dict(feasible=False);continue
            if b>0:
                a,z=pair(p,lo[:9],hi[:9],b-Q('0.0001'))
                need(not all(k==(not up) for k in flags(z if up else a)))
            res[key]=dict(feasible=True,kWh=str(b),history=list(map(str,v)),trailing_sums=list(map(str,totals(v))))
        result[label]=dict(original_flags=flags(p),extrema=res)
    return result
if __name__=='__main__':print(json.dumps(dict(exhaustive=small(),applications=app()),sort_keys=True,indent=2))