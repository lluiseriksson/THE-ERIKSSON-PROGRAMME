"""Checks for the timing envelopes. Run on the programme's Linux runtime."""
from math import exp, expm1, log, isclose
from itertools import product
import json
def verify():
    rates = (0.03, 0.08, 0.15)
    lag_grid = (0, .125, .5, .875, 1)
    totals = (0, 180, 50, 100)
    checked = 0
    for lags in product(lag_grid, repeat=len(totals)):
        for rate in rates:
            q = exp(-rate)
            prev = 0.
            for n,(mass,lag) in enumerate(zip(totals,lags),1):
                now = q*prev + rate*mass*exp(-rate*lag)
                direct = sum(rate*m*exp(-rate*(n-i+ell)) for i,(m,ell) in enumerate(zip(totals[:n],lags[:n]),1))
                assert isclose(now,direct,abs_tol=1e-13)
                integral = prev*(-expm1(-rate))/rate + mass*(-expm1(-rate*lag))
                assert isclose(integral, mass-(now-prev)/rate,abs_tol=5e-13)
                assert q*prev+rate*q*mass-1e-12 <= now <= q*prev+rate*mass+1e-12
                prev=now
                checked+=1
    a,b=.03,.15
    l=exp(-a);power=b/a
    def moment(mu,r):return sum(w*exp(-r*s) for s,w in mu)
    def close(x,y):return isclose(x,y,abs_tol=3e-14,rel_tol=0)
    for i in range(11):
        u=l+(1-l)*i/10
        chord=((1-u)*l**power+(u-l))/(1-l)
        lower=[(-log(u)/a,1)]
        upper=[(1,(1-u)/(1-l)),(0,(u-l)/(1-l))]
        for j in range(11):
            t=j/10
            mix=[(s,(1-t)*w) for s,w in lower]+[(s,t*w) for s,w in upper]
            assert close(moment(mix,a),u)
            assert close(moment(mix,b),(1-t)*u**power+t*chord)
    # Eq.14 endpoint recurrence with n+1 entries versus n monthly totals.
    sample=(70,10,80,45,120)
    for a0 in rates:
        q=exp(-a0); c=0.; upper=0.
        for n in range(len(sample)):
            if n:
                c=q*c+(1-q)*sample[n]
                upper=q*upper+a0*sample[n]
            printed=sum(a0*exp(-a0*(n-j))*sample[j] for j in range(n+1))
            assert close(printed,upper+q**n*a0*sample[0]) or isclose(printed,upper+q**n*a0*sample[0])
            assert isclose(printed,a0*c/(1-q)+q**n*a0*sample[0])
    return dict(endpoint_and_integral_checks=checked,constructed_two_rate_points=121,
                one_month=dict(monthly_total=100,alpha=.15,prior=0,close_rate=[15*exp(-.15),15],
                               spending=[0,100*(-expm1(-.15))],
                               constant_flow_spending=100*(1+expm1(-.15)/.15)),
                rates=list(rates),meaning="synthetic tests on equal one-month intervals; figures not reproduced")
if __name__=="__main__":
    print(json.dumps(verify(),indent=2))
