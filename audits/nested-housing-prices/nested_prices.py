"""Check two reconstructions of the unadjusted regressions in CESifo WP 10746."""
from fractions import Fraction as F
import json
from math import erfc, sqrt


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sensitivity():
    a, b, u, v, h = map(F, ('.355', '.051', '.103', '.014', '.0005'))
    cross_lower = (b-h)*(u-h) - (a+h)*(v+h)
    require(cross_lower == F(43, 2_000_000), 'determinant lower bound')

    def gap(a, b, u, v):
        return 100*((b-v)/(a-u)-b/a)

    lo = gap(a+h, b-h, u-h, v+h)
    hi = gap(a-h, b+h, u+h, v-h)
    l, m = F('.255'), F('.038')
    prose = [100*((m-h)/(l+h)-(b+h)/(a-h)), 100*((m+h)/(l-h)-(b-h)/(a+h))]
    require(0 < lo < hi and 0 < prose[0] < prose[1], 'sign must survive both readings')
    require(a+h-(u-h) < l-h, 'table and narrative overlap')
    return {'table_pp': [float(lo),float(hi)], 'table_exact': [str(lo),str(hi)],
            'prose_pp': list(map(float,prose)), 'prose_exact': list(map(str,prose))}


def witness(five_home, fifty_home, five_let, fifty_let):
    n0, n1 = 1_311_097, 118_000
    n = n0+n1
    require(n == 1_429_097 and 0 < fifty_let < five_let < n1 and
            0 < fifty_home < five_home < n0, 'nested observations')
    fits = []
    for k0,k1,target in [(five_home,five_let,[355,-103,0,1,4]),
                           (fifty_home,fifty_let,[51,-14,0,1,0])]:
        p0,p1=F(k0,n0),F(k1,n1)
        variance=(k0*(1-p0)+k1*(1-p1))/(n-2)
        total_ss=(k0+k1)*(1-F(k0+k1,n))
        adj=1-variance*(n-1)/total_ss
        slope=p1-p0
        se0sq=variance/n0
        se1sq=variance*(F(1,n0)+F(1,n1))
        for value,shown in zip([p0,slope,adj],[target[0],target[1],target[4]]):
            require(abs(value*1000-shown)<F(1,2),'coefficient or adjusted R squared')
        for square,shown in [(se0sq,target[2]),(se1sq,target[3])]:
            require(max(F(0),F(2*shown-1,2000))**2<=square<F(2*shown+1,2000)**2,
                    'pooled OLS standard error')
        fits.append([float(p0),float(slope),sqrt(se0sq),sqrt(se1sq),float(adj)])
    r0,r1=F(fifty_home,five_home),F(fifty_let,five_let)
    pooled=F(fifty_home+fifty_let,five_home+five_let)
    z2=(r1-r0)**2/(pooled*(1-pooled)*(F(1,five_home)+F(1,five_let)))
    z=sqrt(z2)
    return {'rows_home_let': [n0,n1], 'five_home_let': [five_home,five_let],
            'fifty_home_let': [fifty_home,fifty_let], 'fits': fits,'gap_pp': float(100*(r1-r0)),
            'z_squared': str(z2), 'z': z, 'normal_reference_p': erfc(z/sqrt(2))}


if __name__=='__main__':
    low=witness(466082,66224,29852,4250)
    high=witness(464797,67508,29620,4482)
    require(F(low['z_squared']) < F('1.96')**2 < F(high['z_squared']),'opposite decisions')
    print(json.dumps({'bounds':sensitivity(),'witnesses':[low,high]},sort_keys=True,indent=2))

