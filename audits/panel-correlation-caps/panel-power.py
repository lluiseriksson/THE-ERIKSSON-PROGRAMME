"""Exact sensitivity certificate; use Python on the dedicated Colab Linux runtime."""
from fractions import Fraction as F
from itertools import product
from math import isqrt
import json

def form(k,l,budget,cap):
    """Ordered correlation masses. Positive, unit variance errors; k <= l."""
    if not (1<k<=l and 0<=budget<=cap*(k+l)*(k+l-1) and 0<=cap<=1):
        raise ValueError('Infeasible correlation budget')
    n1,n0,nx=k*(k-1),l*(l-1),2*k*l
    h1=min(cap,F(budget,n1));h0=min(cap,F(budget-n1*h1,n0));hx=F(budget-n1*h1-n0*h0,nx)
    if not (0<=hx<=h0<=h1<=cap):raise ArithmeticError('Invalid allocation')
    if (1+(k-1)*h1)*(1+(l-1)*h0)<k*l*hx**2:raise ArithmeticError('Not PSD')
    d=1+F(n1*h1*l/k+n0*h0*k/l-nx*hx,k+l)
    return (h1,h0,hx),d
def root_bounds(squared):
    a=isqrt((squared*10**12).numerator//(squared*10**12).denominator)
    if not F(a,10**6)**2<=squared<F(a+1,10**6)**2:raise ArithmeticError('sqrt')
    return [a,a+1]
def answer(ne,d):
    k,l=7,27;T=k+l;dm=F(952,1)/ne;S=T*(dm-1);rho=S/(T*(T-1));goal=F(1,4)
    def scaled(cap):return d*d*form(k,l,S,cap)[1]/dm
    # Crossing is in the middle regime, election correlations at cap, zero cross correlations.
    baseline=1+S*F(k,l*T)
    slope=F(k*(k-1),T)*(F(l,k)-F(k,l))
    cap=(dm*(goal/d)**2-baseline)/slope
    if not (rho<cap<1 and scaled(cap)==goal**2):raise ValueError('Threshold branch changed')
    return dict(mean_factor=str(dm),rho=str(rho),critical_cap=str(cap),uniform=root_bounds(scaled(rho)),uncapped=root_bounds(scaled(F(1))),cap_half=root_bounds(scaled(F(1,2))),cap_seven_tenths=root_bounds(scaled(F(7,10))),worst_correlations=[str(x) for x in form(k,l,S,F(1))[0]])
def main():
    rows=[answer(n,d) for n,d in product([F(717,2),F(719,2)],[F(195,1000),F(205,1000)])]
    centre=answer(F(359),F(1,5))
    # Brute enumeration of the three mass classes in small integer grids, independent of PSD.
    tested=0
    for k,l in [(2,3),(3,5),(4,4)]:
        caps=[k*(k-1),l*(l-1),2*k*l]
        for h in [F(1,4),F(1,2),F(1)]:
            best={}
            for a,b,c in product(*(range(int(n*h*4)+1) for n in caps)):
                s=F(a+b+c,4)
                val=1+(a*F(l,k)+b*F(k,l)-c)/(4*(k+l))
                best[s]=max(best.get(s,val),val)
            for s,d in best.items():
                if form(k,l,s,h)[1]!=d:raise ArithmeticError('Brute budget mismatch')
                tested+=1
    return dict(exact=centre,rounding_corners=rows,checked_small_budgets=tested)
if __name__=='__main__':print(json.dumps(main()))
