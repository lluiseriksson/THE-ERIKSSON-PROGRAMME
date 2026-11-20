from fractions import Fraction as Q
from itertools import product
import json

def need(v,msg):
    if not v:raise ValueError(msg)

def enumerate_gain(T,R,P,S,b,x,rho,eps,conditional):
    # A type of opponent, their visibility draw, the deviator's visibility
    # draw, then their own bypass. Optimize all four discretionary plans.
    plans=[]
    for actions in product((False,True),repeat=2):
        value=0
        for other,sees,seen,bypass in product((False,True),repeat=4):
            prob=1
            for bit,p in zip((other,sees,seen,bypass),(x,rho,rho,eps)):
                prob*=p if bit else 1-p
            opponent_C=other and sees
            own_C=not bypass or actions[int(seen)]
            value+=prob*((R+b*conditional if opponent_C else S) if own_C else (T if opponent_C else P))
        plans.append(value-P)
    return max(plans)

def check():
    T,R,P,S,b=5,3,1,0,3
    count=0
    for x,rho,eps in product([Q(1,12),Q(1,6),Q(1,3)],[Q(1,4),Q(27,29),Q(1)],[Q(0),Q(1,10),Q(2,5)]):
        for cond in (False,True):
            formula=(1-eps)*(S-P+rho*x*(R+cond*b-S))+eps*rho*x*(T-P)
            need(enumerate_gain(T,R,P,S,b,x,rho,eps,cond)==formula,'Enumerator disagreement')
            count+=1
    pars=(T,R,P,S,b,Q(1,6),Q(27,29),Q(1,10))
    example=[enumerate_gain(*pars,c) for c in (True,False)]
    need(example[0]==0 and example[1]<0,'Equality and selfish gain')
    return dict(type_specific_checks=count,example_gains=list(map(str,example)),scope='Unilateral deviation gains from defensive all-A pooling')
if __name__=='__main__':print(json.dumps(check(),sort_keys=True))

