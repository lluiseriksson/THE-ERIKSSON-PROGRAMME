"""Rational enclosures for sharp zero-event upper endpoints, with independent optimizer checks."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import prod
import json
import numpy as np
from scipy.optimize import minimize
alpha=F(1,20)
def balanced(n,k):
    base,extra=divmod(n,k)
    return [base+1]*extra+[base]*(k-extra)
def endpoint(sizes):
    sizes=[F(x) for x in sizes if x]
    total=sum(sizes);lo=F();hi=max(sizes)
    if not total:raise ValueError('Empty group')
    for _ in range(80):
        t=(lo+hi)/2
        if prod(min(F(1),t/n) for n in sizes)<alpha:lo=t
        else:hi=t
    def risk(t):return sum(max(F(0),n-t) for n in sizes)/total
    return risk(hi),risk(lo)
def numerical(sizes):
    v=np.array(sizes,dtype=float);w=v/v.sum()
    # Optimize over -log(q), on a simplex.
    r=minimize(lambda x:w@np.exp(-x),np.full(len(v),-np.log(float(alpha))/len(v)),
               jac=lambda x:-w*np.exp(-x),bounds=[(0,-np.log(float(alpha)))]*len(v),
               constraints=[dict(type='eq',fun=lambda x:sum(x)+np.log(float(alpha)),jac=lambda x:np.ones(len(v)))],
               method='SLSQP',options=dict(ftol=1e-13,maxiter=200))
    if not r.success:raise ValueError(r.message)
    return 1-r.fun
def fmt(interval):
    lo,hi=interval
    return dict(lower=str(lo),upper=str(hi),percent_lower=(lo*1000000).__floor__()/10000,percent_upper=(hi*1000000).__ceil__()/10000)
odd=balanced(58,21);even=balanced(52,22)
profiles={'independent_units':[1]*110,'43_equal_weights':[1]*43,'integer_plate_floor':odd+even,'odd':odd,'even':even,'one_plate':[110]}
out={}
for key,sizes in profiles.items():
    a,b=endpoint(sizes);v=numerical(sizes)
    if abs(v-float((a+b)/2))>1e-7:raise ArithmeticError(key)
    out[key]=fmt((a,b))
out['fold_floor']=fmt(tuple((58*a+52*b)/110 for a,b in zip(endpoint(odd),endpoint(even))))
count=0
for n in range(3,12):
    for k in range(2,min(n,5)+1):
        best=endpoint(balanced(n,k))
        for sizes in combinations_with_replacement(range(1,n),k):
            if sum(sizes)!=n:continue
            observed=endpoint(sizes)
            if observed[1]<best[0]:raise ArithmeticError('Balance inequality')
            count+=1
# Direct attainable boundary for the best allocation, where only triples contribute.
witness=1-float(alpha)**(1/24)
if abs(72/110*witness-float(endpoint(odd+even)[0]))>1e-10:raise ArithmeticError('Extremizer')
if not (F(97,100)**98>alpha>F(97,100)**99):raise ArithmeticError('Cluster count threshold')
print(json.dumps(dict(results=out,odd_sizes=odd,even_sizes=even,balanced_checks=count,boundary_risk_triple=witness,one_sided_alpha=str(alpha),minimum_equal_groups_for_three_percent=99)))