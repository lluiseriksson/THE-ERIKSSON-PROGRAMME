"""Verify every pure device and continuation deviation for a positive-adoption example."""
from fractions import Fraction as F
from itertools import product
import json

x=F(3,5);rho=F(1,4);m=F(2,3)
# Rule for an A user in signal order observed A, observed M, and unobserved.
def payoff(kind,commit,rule,material=False):
    result=F(0)
    for typ,share in ((True,x),(False,1-x)):
        adopter=m if typ else F(0)
        for other_commit,prob in ((True,adopter),(False,1-adopter)):
            for see,p1 in ((True,rho),(False,1-rho)):
                action=commit or rule[int(other_commit) if see else 2]
                for seen,p2 in ((True,rho),(False,1-rho)):
                    coop=other_commit or (typ and seen and commit)
                    value=(3 if coop else 0) if action else (5 if coop else 1)
                    if not material and kind and coop and action:value+=3
                    result+=share*prob*p1*p2*value
    return result
theta=(0,1,0);tau=(0,0,0)
adoption=payoff(True,True,theta);disc=payoff(True,False,theta);selfish=payoff(False,False,tau)
for kind,baseline in ((True,disc),(False,selfish)):
    deviations=[payoff(kind,False,z) for z in product((0,1),repeat=3)]+[payoff(kind,True,tau)]
    if max(deviations)!=baseline:raise ValueError('Profitable deviation')
gap=m*payoff(True,True,theta,True)+(1-m)*payoff(True,False,theta,True)-selfish
if not (adoption==disc and payoff(False,True,tau)<selfish and gap<0 and x*m==F(2,5)):raise ValueError('Mixed support')
print(json.dumps(dict(share=str(x),observation=str(rho),theta_adoption=str(m),population_adoption=str(x*m),utility_when_committed=str(adoption),utility_when_discretionary=str(disc),selfish_utility=str(selfish),selfish_deviation=str(payoff(False,True,tau)),fitness_gap=str(gap),checked='All eight discretionary signal rules plus the committed device for both types.'),indent=2))