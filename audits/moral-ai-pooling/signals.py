"""Direct two-player signal enumeration for the two extreme adoption profiles."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
from coexistence import check, need

T,R,P,S,b=Q(301,100),3,1,0,Q(7,10)
x,eps=Q(11,20),Q(1,4)
h=1-eps
q=h+eps*x

def margins(channels,pool,choice,theta):
    # Compute the best free action at each signal, allowing all actions at
    # every signal. A forced action contributes separately to expected utility.
    vals={}
    for observed,ps in enumerate(channels[pool]):
        if not ps:continue
        forced_value,cooperate,defect=0,0,0
        for partner_type,partner_bypass in product((0,1),repeat=2):
            for received,chance in enumerate(channels[choice]):
                probability=ps*chance*(x if partner_type else 1-x)*(eps if partner_bypass else h)
                # A free conditional partner behaves as if it faced pool on
                # its support, and the other label at exclusive signals.
                thinks_M=pool if channels[pool][received] else 1-pool
                other=(pool and not partner_bypass) or (partner_type and thinks_M)
                C=R+theta*b if other else S
                D=T if other else P
                forced_value+=probability*C
                cooperate+=probability*C
                defect+=probability*D
        vals[observed]=(h*forced_value+eps*max(cooperate,defect)) if choice else max(cooperate,defect)
    return sum(vals.values())

def experiment(channels):
    a,m=channels
    need(all(sum(row)==1 and all(p>=0 for p in row) for row in channels),'Bad channel')
    dm=sum(v for v,u in zip(m,a) if u==0)
    da=sum(v for v,u in zip(a,m) if u==0)
    cost=(1-q)*(P-S)+q*(T-R)
    out={}
    for pool,theta in product((0,1),repeat=2):
        direct=margins(channels,pool,pool,theta)-margins(channels,pool,1-pool,theta)
        if pool: expected=da*eps*x*(R+b-S) if theta else da*eps*x*(T-P)-h*cost
        else: expected=h*(P-S)-dm*x*(h*(R+theta*b-S)+eps*(T-P))
        need(direct==expected,'Signal-contingent margins disagree')
        out[('M' if pool else 'A')+(' conditional' if theta else ' selfish')]=str(direct)
    return dict(only_M=str(dm),only_A=str(da),margins=out)

def main():
    r=Q(2,5);channels={}
    channels['erasure']=([r,0,1-r],[0,r,1-r])
    eta=Q(1,10000)
    channels['false_reports']=([r*(1-eta),r*eta,1-r],[r*eta,r*(1-eta),1-r])
    channels['one_sided']=([r,0,1-r],[r*eta,r*(1-eta),1-r])
    channels['unequal_diagnostics']=([Q(1,2),0,Q(1,4),Q(1,4)],[0,Q(1,3),Q(4,9),Q(2,9)])
    results={name:experiment(rows) for name,rows in channels.items()}
    need(results['erasure']['margins']==check()['example_margins'],'Base case mismatch')
    need(Q(results['false_reports']['margins']['M selfish'])<0,'Full-support counterexample')
    return dict(base=check(),signal_channels=results)
if __name__=='__main__': print(json.dumps(main(),indent=2,sort_keys=True))
