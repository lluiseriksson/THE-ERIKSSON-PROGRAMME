"""Verify deviations in the two pooling profiles directly from the signal game."""
from fractions import Fraction as F
from itertools import product
import json

# Action rules specify what to do if the opponent's technology is A, M, or hidden.
# Selfish and conditional types face the same material payoff matrix.
def audit(game,rho,x,cooperative):
    T,R,P,S,b=game
    rules=list(product((0,1),repeat=3))
    def expected(kind,device,rule,utility):
        val=0
        for other,prob in [(1,x),(0,1-x)]:
            for informed,p1 in [(True,rho),(False,1-rho)]:
                own=1 if device=='M' else rule[0 if informed else 2]
                for seen,p2 in [(True,rho),(False,1-rho)]:
                    opponent=int(other and ((device=='M' and seen) or cooperative))
                    material=(R if opponent else S) if own else (T if opponent else P)
                    val+=prob*p1*p2*(material+int(utility and kind and own and opponent)*b)
        return val
    status={}
    for kind in (0,1):
        baseline=(int(kind and cooperative),kind,int(kind and cooperative))
        u=expected(kind,'A',baseline,True)
        alternatives=[expected(kind,'A',rule,True) for rule in rules]+[expected(kind,'M',None,True)]
        status[kind]=(u>=max(alternatives),expected(kind,'A',baseline,False))
    return all(ok for ok,v in status.values()),status[1][1]-status[0][1]

games=[(5,3,1,0,3),(8,5,3,1,7),(7,4,2,-1,4),(9,3,1,-2,8)]
stats=dict(cases=0,defensive=0,cooperative=0,coexist=0,on_k=0,on_c=0)
example=[]
for game in games:
    T,R,P,S,b=game;p=P-S;h=R+b-T;L=R+b-S;k=F(p,p+h);boundary=F(p+h,L)
    for rho in sorted({boundary,boundary/2,boundary/3,F(1,4)}):
        if rho>boundary:continue
        c=F(p,L)/rho
        for x in sorted({k,c,*[F(j,12) for j in range(1,12)],min(k,c)/2,(k+min(1,c))/2}):
            if not 0<x<1:continue
            defend,gapd=audit(game,rho,x,False)
            coop,gapc=audit(game,rho,x,True)
            if defend!=(x<=c) or coop!=(x>=k) or gapd!=0 or gapc!=x*(R-T)+(1-x)*(S-P):raise ValueError((game,rho,x,defend,coop))
            stats['cases']+=1;stats['defensive']+=int(defend);stats['cooperative']+=int(coop)
            stats['coexist']+=int(defend and coop);stats['on_k']+=int(x==k);stats['on_c']+=int(x==c)
            if game==games[0] and rho==F(1,4) and x in (k,c):
                example.append(dict(x=str(x),zero_gap=str(gapd),negative_gap=str(gapc)))
print(json.dumps(dict(pooling=stats,games=games,reference_example=example,interpretation='Pure device and contingent action deviations at the pooling profiles. Mixed deviations follow by linearity. This finite panel does not enumerate mixed equilibria.'),indent=2))