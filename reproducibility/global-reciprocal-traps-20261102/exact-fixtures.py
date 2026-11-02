"""Exact finite diagnostic fixtures, not a proof of the asymptotic theorem.
Run only in own Colab Linux. No acceptance depends on Python assert.
"""
from fractions import Fraction as F
from itertools import product
import copy,json,sys

def shift(x,i,sign,n):
    y=list(x);y[i]=(y[i]+sign)%n;return tuple(y)

def make_fixture(D,L,n,centres,m=None):
    if D<3 or L<1 or n%(2*L+2):raise ValueError('fixture domain')
    points=list(product(range(-L+1,L),repeat=D))
    fields=[];weak=set()
    for y in centres:
        psi={tuple((y[i]+z[i])%n for i in range(D)):
             __import__('functools').reduce(lambda a,b:a*b,(F(L-abs(t),L) for t in z),F(1)) for z in points}
        u={}
        for j,k,sign in [(0,1,1),(1,0,-1)]:
            candidates=set(psi)|{shift(x,k,1,n) for x in psi}
            for x in candidates:
                val=sign*(psi.get(x,F(0))-psi.get(shift(x,k,-1,n),F(0)))
                if val:u[(x,j)]=val
        fields.append(u)
        weak.update(tuple((y[i]+z[i])%n for i in range(D)) for z in product(range(-L,L+1),repeat=D))
    s=F(len(weak),n**D)
    if m is None:m=1/s
    m=F(m);strong=(m-s)/(1-s)
    return dict(D=D,L=L,n=n,centres=centres,fields=fields,weak=weak,m=m,strong=strong)

def verify(f):
    D,L,n=f['D'],f['L'],f['n'];fields=f['fields'];weak=f['weak'];m=f['m'];A=f['strong']
    if not fields or len(weak)!=(2*L+1)**D*len(fields):raise ValueError('weak box count/disjointness')
    s=F(len(weak),n**D)
    if not (1<=m and 1<=A<=2*m):raise ValueError('positive repair or upper bound')
    if s+(1-s)*A!=m:raise ValueError('actual arithmetic mean')
    inv=s+(1-s)/A
    if inv>2/m:raise ValueError('actual reciprocal mean')
    T=F(2*L*L+1,3*L);V=F(2,L);W=F(6,L*L)
    expected_norm=2*V*T**(D-1)
    expected_energy=2*(W*T**(D-1)+(D-1)*V*V*T**(D-2))
    ratio=F(3,L)+F(6*(D-1),2*L*L+1)
    if expected_energy/expected_norm!=ratio or ratio>F(3*D,L):raise ValueError('hat algebra')
    all_support=[];all_gradient=[]
    def metrics(u):
        support={x for x,j in u};divsites=set(support)
        for x,j in u:divsites.add(shift(x,j,1,n))
        for x in divsites:
            div=sum((u.get((x,j),F(0))-u.get((shift(x,j,-1,n),j),F(0)) for j in range(D)),F(0))
            if div:raise ValueError('actual backward divergence')
        gradient=set(support)
        for x in support:
            for i in range(D):gradient.add(shift(x,i,-1,n))
        energy=F(0);active=set()
        for x in gradient:
            for i in range(D):
                for j in range(D):
                    d=u.get((shift(x,i,1,n),j),F(0))-u.get((x,j),F(0))
                    if d:
                        active.add(x);energy+=(1 if x in weak else A)*d*d
        if not active<=weak:raise ValueError('gradient support escapes weak boxes')
        norm=sum((v*v for v in u.values()),F(0))
        if norm<=0:raise ValueError('zero field')
        return norm,energy,support,active
    for u in fields:
        norm,energy,support,gradient=metrics(u)
        if norm!=expected_norm or energy!=expected_energy:raise ValueError('counting energy/norm')
        for old in all_support:
            if old&support:raise ValueError('overlapping field supports')
        for old in all_gradient:
            if old&gradient:raise ValueError('overlapping gradient supports')
        all_support.append(support);all_gradient.append(gradient)
    combo={}
    coeff=[2,-3]+[1]*max(0,len(fields)-2)
    for t,u in zip(coeff,fields):
        for key,v in u.items():combo[key]=combo.get(key,F(0))+t*v
    norm,energy,_,_=metrics(combo)
    scale=sum(t*t for t in coeff[:len(fields)])
    if norm!=scale*expected_norm or energy!=scale*expected_energy:raise ValueError('span identity')
    return dict(D=D,L=L,n=n,traps=len(fields),m=str(m),weak_sites=len(weak),inverse_mean=str(inv),
                squared_norm=str(expected_norm),energy=str(expected_energy),rayleigh=str(ratio),
                all_actual_divergences_zero=True,span_identity=True)

def main():
    fixtures=[]
    for D,L in [(3,1),(3,2),(3,3),(4,1),(4,2)]:
        P=2*L+2;n=2*P;y=(L,)*D;z=(L+P,)+(L,)*(D-1)
        fixtures.append(make_fixture(D,L,n,[y,z]))
    fixtures.append(make_fixture(3,1,56,[(1,1,1),(5,1,1)],m=56**2))
    accepted=[];rejected=0
    for f in fixtures:
        accepted.append(verify(f))
        bad=copy.deepcopy(f);key=next(iter(bad['fields'][0]));bad['fields'][0][key]+=1
        bad2=copy.deepcopy(f);bad2['strong']+=1
        bad3=copy.deepcopy(f);bad3['weak'].remove(next(iter(bad3['weak'])))
        for mutation in [bad,bad2,bad3]:
            try:verify(mutation)
            except ValueError:rejected+=1
            else:raise RuntimeError('Real field/profile/support mutation accepted')
    if len(accepted)!=6 or rejected!=18:raise RuntimeError('Wrong acceptance/rejection count')
    print(json.dumps(dict(status='EXACT_FINITE_FIXTURES_ACCEPTED',fixtures=accepted,accepted=6,
                         real_mutations_rejected=18,optimized=not __debug__,general_theorem_verified=False),indent=2))
if __name__=='__main__':main()