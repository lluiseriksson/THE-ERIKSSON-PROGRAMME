"""Principal payment schedules for three exponential response rates."""
from fractions import Fraction
from mpmath import mp
import json

mp.dps = 65

def chord(u, left, right, power):
    if left == right:
        return left**power
    return ((right-u)*left**power + (u-left)*right**power)/(right-left)

def support_root(u, v, power, left, right, fixed_left):
    for _ in range(180):
        mid = (left+right)/2
        low, high = (fixed_left, mid) if fixed_left is not None else (mid, mp.mpf(1))
        value = chord(u, low, high, power)
        if (value < v) == (fixed_left is not None):
            left = mid
        else:
            right = mid
    return (left+right)/2

def extremes(L, p, r, u, v):
    if not (0 < L < 1 and 1 < p < r and L <= u <= 1):
        raise ValueError("Invalid rates, support or mean")
    minimum, maximum = u**p, chord(u,L,1,p)
    if not minimum <= v <= maximum:
        raise ValueError("Infeasible input moments")
    if u == L or u == 1 or v == minimum:
        return u**r,u**r
    if v == maximum:
        y = chord(u,L,1,r)
        return y,y
    z = support_root(u,v,p,u,mp.mpf(1),L)
    t = support_root(u,v,p,L,u,None)
    return chord(u,L,z,r),chord(u,t,1,r)

def verify():
    F=Fraction
    L,u,v=F(1,2),F(3,4),F(19,32)
    ll,rr=chord(u,L,F(7,8),3),chord(u,F(5,8),1,3)
    assert chord(u,L,F(7,8),2)==v==chord(u,F(5,8),1,2)
    assert ll==F(125,256) and rr==F(127,256)
    wrong=F(1,2)
    assert max(u**3,0)<wrong<min(chord(u,L,1,3), ((1-v)*L**3+(v-L**2))/(1-L**2))
    assert v**3<wrong**2 and rr<wrong
    # Polynomial certificate for the upper bound at the same rational input:
    # (1-X)(X-5/8)^2 >= 0, with equality on the proposed support.
    z=F(7,8)
    assert (L+2*z)*v-(2*L*z+z*z)*u+L*z*z == ll
    t=F(5,8)
    assert (1+2*t)*v-(2*t+t*t)*u+t*t == rr
    lo,hi=extremes(mp.mpf('.5'),2,3,mp.mpf('.75'),mp.mpf(19)/32)
    assert abs(lo-mp.mpf(ll.numerator)/ll.denominator)<mp.mpf('1e-48')
    assert abs(hi-mp.mpf(rr.numerator)/rr.denominator)<mp.mpf('1e-48')
    a,b,c=map(mp.mpf,['.03','.08','.15'])
    L=mp.exp(-a);p=b/a;r=c/a
    one=mp.mpf(1);checked=0
    for lag1 in ['0','.25','.5']:
        for lag2 in ['.60','.75','1']:
            for w in ['.2','.4','.8']:
                x,y=mp.exp(-a*mp.mpf(lag1)),mp.exp(-a*mp.mpf(lag2))
                w=mp.mpf(w)
                mean=lambda k:w*x**k+(1-w)*y**k
                u1,v1=mean(1),mean(p)
                if x==1 and y==L:
                    # The input is an endpoint mixture exactly. Independent rounded
                    # evaluations may differ in the final working-precision digit.
                    vmax=chord(u1,L,1,p)
                    assert abs(v1-vmax) < mp.mpf('1e-60')
                    v1=vmax
                lo,hi=extremes(L,p,r,u1,v1)
                assert lo-mp.mpf('1e-48')<=mean(r)<=hi+mp.mpf('1e-48')
                checked+=1
    u=(1+L)/2;v=(u**p+chord(u,L,1,p))/2
    lo,hi=extremes(L,p,r,u,v)
    pairlo=max(u**r,v**(r/p));pairhi=min(chord(u,L,one,r),chord(v,L**p,one,r/p))
    wrong=(hi+pairhi)/2
    assert pairlo < lo < hi < wrong < pairhi
    fmt=lambda x:mp.nstr(x,32)
    return dict(rational_example=dict(L='1/2',p=2,r=3,u='3/4',v='19/32',sharp=[str(ll),str(rr)],pairwise_false_positive='1/2'),source_rate_example=dict(rates=['0.03','0.08','0.15'],u=fmt(u),v=fmt(v),sharp=[fmt(lo),fmt(hi)],pairwise=[fmt(pairlo),fmt(pairhi)],false_positive=fmt(wrong),period_months=1),additional_payment_mixtures=checked)
if __name__=='__main__':
    print(json.dumps(verify(),indent=2))
