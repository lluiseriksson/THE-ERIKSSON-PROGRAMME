"""Construct an equilibrium and verify both types' deviations at every signal."""
from fractions import Fraction as F
import json
from signals import main as check_pooling

def need(test,message):
    if not test:
        raise ValueError(message)

def witness(eta):
    T,R,P,S,b = F(301,100),3,1,0,F(7,10)
    x,rho,eps = F(11,20),F(2,5),F(1,4)
    h=1-eps
    Y,D,H=P-S,T-R,T-P
    k=Y/(R+b-T+Y)
    alpha=rho*eta
    diff=rho*(1-2*eta)
    r=alpha/diff
    q=h+eps*x
    Q=(q+h*r*(1-Y/H))/(1+h*r*(1/k+(D-Y)/H))
    mass=r*(Q-k)/k
    abstain=h*((1-Q)*Y+Q*D)/(x*eps*diff*H)
    need(0<mass<1-x and 0<abstain<1,'Interior mixing')
    laws={'M':{'a':alpha,'m':rho-alpha,'n':1-rho},
          'A':{'a':rho-alpha,'m':alpha,'n':1-rho}}
    pay={}
    for own in ('A','M'):
        for theta in (False,True):
            value=0
            for s in ('a','m','n'):
                # Sum the joint probability of each signal and partner action,
                # using only primitive independent draws and prescribed plans.
                total=coop=0
                for share,label,partner_cond in ((x,'M',True),(1-x-mass,'M',False),(mass,'A',False)):
                    for partner_signal,prob in laws[own].items():
                        for bypass,fprob in ((True,eps),(False,h)):
                            weight=share*laws[label][s]*prob*fprob
                            if label=='M' and not bypass:action=1
                            elif partner_cond:action=1-abstain if partner_signal=='a' else 1
                            else:action=0
                            total+=weight
                            coop+=weight*action
                cu=coop*(R+theta*b)+(total-coop)*S
                du=coop*T+(total-coop)*P
                if own=='M' and theta:
                    if s=='a':need(cu==du,'Conditional user must be indifferent at report a')
                    else:need(cu>du,'Conditional user must cooperate')
                if not theta:need(du>cu,'Selfish user must defect')
                value+=(h*cu+eps*max(cu,du)) if own=='M' else max(cu,du)
            pay[(own,theta)]=value
    margin=pay['M',True]-pay['A',True]
    need(margin>0 and pay['M',False]==pay['A',False],'Label deviations')
    return dict(eta=str(eta),unrestricted_mass=str(mass),opt_out_probability_if_selfish=str(mass/(1-x)),
                probability_defect_after_a_if_free_conditional=str(abstain),
                conditional_label_margin=str(margin),selfish_label_margin='0')

if __name__=='__main__':
    print(json.dumps(dict(pooling=check_pooling(),near_universal=[witness(F(1,n)) for n in (100,1000,10000,100000)]),indent=2,sort_keys=True))
