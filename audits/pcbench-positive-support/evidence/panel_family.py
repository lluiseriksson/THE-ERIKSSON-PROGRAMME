"""Simultaneous decisions on the disclosed rank intervals. All comparisons are rational."""
import json
from math import comb
from fractions import Fraction as F
from scipy.stats import hypergeom
data=json.load(open('panel-identification.json'))['rows']
def tail(n,h,r):
    if n==0:return F(1)
    k=min(50,n)
    return sum(F(comb(h,j)*comb(n-h,k-j),comb(n,k)) for j in range(max(r,0,k+h-n),min(k,h)+1))
def holm(p):
    ordered=sorted(p,key=lambda k:(p[k],k));m=len(p);result=[]
    for j,k in enumerate(ordered):
        if p[k]>F(1,20*(m-j)):break
        result.append(k)
    # Equivalent closed step-down adjusted p-values, evaluated by exact arithmetic.
    adjusted={};last=F()
    for j,k in enumerate(ordered):
        last=max(last,min(F(1),(m-j)*p[k]));adjusted[k]=last
    assert set(result)=={k for k,v in adjusted.items() if v<=F(1,20)}
    return sorted(result)
nom={};lo={};hi={};cuts={}
for k,x in data.items():
    a=x['size_lower'];b=x['size_upper'];h=x['positive_controls'];r=x['positive_hits']
    low=lo[k]=tail(b,h,r);high=hi[k]=tail(a,h,r);nom[k]=tail(x['G'],x['panel'],x['observed'])
    assert abs(float(low)-x['p_min'])<1e-12 and abs(float(high)-x['p_max'])<1e-12
    if low<F(1,20)<=high:
        i,j=a,b
        while j-i>1:
            mid=(i+j)//2
            if tail(mid,h,r)<F(1,20):j=mid
            else:i=mid
        assert tail(j,h,r)<F(1,20)<=tail(j-1,h,r)
        cuts[k]=j
nominal=holm(nom);lower=holm(hi);upper=holm(lo)
assert set(lower)<=set(upper) and len(cuts)==25
print(json.dumps(dict(total=len(data),holm_full=nominal,holm_guaranteed=lower,holm_outer=upper,nominal_threshold_support=cuts,full_not_even_in_outer=sorted(set(nominal)-set(upper)),guaranteed_absent_full=sorted(set(lower)-set(nominal))),sort_keys=True))
