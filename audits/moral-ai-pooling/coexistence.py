"""Pure adoption and all contingent discretionary plans in either pooling regime."""
from fractions import Fraction as Q
from itertools import product
import json

def need(ok, message):
    if not ok:
        raise ValueError(message)

def utilities(pool, choice, theta, T, R, P, S, b, x, rho, eps):
    # In either pool a free conditional opponent cooperates upon seeing M,
    # defects upon seeing A, and follows the equilibrium pool if unobserved.
    plans = {}
    for plan in product((0, 1), repeat=2):
        utility = 0
        for state in product((0, 1), repeat=5):
            partner_theta, sees_partner, seen_by_partner, free, partner_free = state
            probability = 1
            for flag, chance in zip(state, (x,rho,rho,eps,eps)):
                probability *= chance if flag else 1-chance
            other = (pool and not partner_free) or (partner_theta and (choice if seen_by_partner else pool))
            own = (choice and not free) or plan[sees_partner]
            utility += probability * ((R+theta*b if other else S) if own else (T if other else P))
        plans[''.join(map(str,plan))] = utility
    return plans

def run_profile(T,R,P,S,b,x,rho,eps):
    h = 1-eps
    kappa = Q(P-S,R+b-T+P-S)
    need(x<kappa<h and eps>0,'Domain')
    q = h+eps*x
    cost = (1-q)*(P-S)+q*(T-R)
    # Payoffs from the pooled label minus the best deviation to the other label.
    margins = {}
    for pool,theta in product((0,1),repeat=2):
        args = (theta,T,R,P,S,b,x,rho,eps)
        own = utilities(pool,pool,*args)
        alt = utilities(pool,1-pool,*args)
        on_path = own['11' if pool and theta else '00']
        need(on_path==max(own.values()),'A discretionary action deviation beats the prescribed plan')
        m = on_path-max(alt.values())
        if pool:
            expected = rho*eps*x*(R+b-S) if theta else rho*eps*x*(T-P)-h*cost
        else:
            expected = h*(P-S)-rho*x*(h*(R+theta*b-S)+eps*(T-P))
        need(m==expected,'Four-plan and closed-form margins disagree')
        margins[('M' if pool else 'A')+(' conditional' if theta else ' selfish')]=str(m)
    material_gap=utilities(1,1,0,T,R,P,S,b,x,rho,eps)['00']-utilities(1,1,0,T,R,P,S,b,x,rho,eps)['11']
    need(material_gap==eps*cost,'Material fitness difference')
    return margins,str(material_gap)

def check():
    T,R,P,S,b=Q(301,100),3,1,0,Q(7,10)
    x,rho,eps=Q(11,20),Q(2,5),Q(1,4)
    margins, gap = run_profile(T,R,P,S,b,x,rho,eps)
    need(all(Q(m)>0 for m in margins.values()),'Named pair of strict adoption equilibria')
    h=1-eps; q=h+eps*x
    L=h*((1-q)*(P-S)+q*(T-R))/(eps*x*(T-P))
    U=h*(P-S)/(x*(h*(R+b-S)+eps*(T-P)))
    need(0<L<rho<U<1,'Nonempty strict interval')
    for boundary, label in [(L,'M selfish'),(U,'A conditional')]:
        at,_=run_profile(T,R,P,S,b,x,boundary,eps)
        need(Q(at[label])==0,'Boundary indifference')
    count=0
    for t,xv,rv,ev in product((Q(301,100),Q(31,10)),(Q(1,3),Q(11,20)),(Q(1,8),Q(2,5),Q(4,5)),(Q(1,100),Q(1,4))):
        run_profile(t,R,P,S,b,xv,rv,ev)
        count+=1
    return dict(profile_grid=count,example_margins=margins,example_selfish_fitness_advantage=gap,
                visibility_interval=[str(L),str(U)],example_q=str(q),boundary_checks=2)
if __name__=='__main__':
    print(json.dumps(check(),indent=2,sort_keys=True))
