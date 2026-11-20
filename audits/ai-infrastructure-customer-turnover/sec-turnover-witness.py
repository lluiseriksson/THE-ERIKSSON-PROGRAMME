"""Construct feasible revenue-allocation witnesses at both ends of a proposed interval.

Run on dedicated Colab. Ratios use the exact displayed revenue totals, an admissible
choice if those totals themselves were rounded. Endpoints are tested as limits.
"""
from fractions import Fraction as F
from pathlib import Path
import json

def check(ok, cause):
    if not ok:
        raise ValueError(cause)

def witness(bound, epsilon):
    if bound == 'lower':
        a,b,c=F(355,10)+epsilon,F(26),F(10)
        a3,b3,c3=F(245,10)-epsilon,F(30),F(10)-epsilon
        q2=[a,b,c]+[(100-a-b-c)/6]*6
        q3=[a3,b3,c3]+[(100-a3-b3-c3)/6]*6
        half=[F(40),F(23),F(8)]+[F(29,6)]*6
    else:
        a,b,c=F(36),F(255,10)+epsilon,F(10)
        a3,b3=F(235,10)+epsilon,F(30)
        q2=[a,b,c]+[(100-a-b-c)/4]*4+[F(0)]*6
        q3=[a3,b3]+[F(0)]*5+[(100-a3-b3)/6]*6
        half=[F(40),F(23),F(6)]+[F(5)]*4+[F(11,6)]*6
    # Use the first quarter only to certify feasibility of each reported H1 proportion.
    q1=[(4653*h-2575*x)/2078 for h,x in zip(half,q2)]
    nine=[(4653*h+3661*y)/8314 for h,y in zip(half,q3)]
    for seq in [q1,q2,q3,half,nine]:
        check(sum(seq)==100 and min(seq)>=0,'Infeasible periods')
    for seq,reported in [(q2,[36,26,10]),(q3,[24,30]),(half,[40,23]),(nine,[33,26])]:
        check(all(v>=10 and abs(v-target)<F(1,2) for v,target in zip(seq,reported)),'Published interval')
        check(max(seq[len(reported):])<10,'Unreported customer exceeds threshold')
    turnover=sum(abs(x-y) for x,y in zip(q2,q3))/2
    target=11+3*epsilon if bound=='lower' else 51-2*epsilon
    check(turnover==target,'Turnover formula')
    return {key:[str(v) for v in seq] for key,seq in [('Q1',q1),('Q2',q2),('Q3',q3),('H1',half),('9M',nine)]}|{'turnover_pct':str(turnover)}

if __name__=='__main__':
    for denominator in [100,1000,10000]:
        eps=F(1,denominator)
        for side in ['lower','upper']:
            print(json.dumps({'family':side,'epsilon':str(eps),'witness':witness(side,eps)},sort_keys=True))


    # Conservatively allow independent half-million rounding on the revenue totals.
    t,h,q=F(8314),F(4653),F(3661)
    d=F(1,2)
    for key,s9,s3,lo,hi in [('A',33,24,30,50),('B',26,30,15,30)]:
        lower=((t-d)*(s9-d)-(q+d)*(s3+d))/(h+d)
        upper=((t+d)*(s9+d)-(q-d)*(s3-d))/(h-d)
        check(lo<lower<=upper<hi,'Unexpected implied H1')
        allowed=[tag for tag,l,u in [('A',F(395,10),F(405,10)),('B',F(225,10),F(235,10)),('other',0,10)] if max(lower,l)<=min(upper,u)]
        check(allowed==[key],'Cross-quarter anonymous linkage ambiguous')
        print(json.dumps(dict(label=key,implied_H1=[str(lower),str(upper)],matches=allowed),sort_keys=True))
    check((F(355,10)**2+F(255,10)**2+10**2)-(F(305,10)**2+F(245,10)**2+4*10**2+5**2)==55,'HHI bound')
