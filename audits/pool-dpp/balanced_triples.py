"""Recover the marginal Taylor coefficients by direct rational multinomial quadrature."""
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import combinations
from math import comb, prod
import json

DIM = 6
TRIPLES = tuple(combinations(range(DIM), 3))
M = len(TRIPLES)

def require(condition, why):
    if not condition:
        raise ValueError(why)

def counts(n, d):
    if d == 1:
        yield (n,)
        return
    for first in range(n+1):
        for tail in counts(n-first, d-1):
            yield (first,) + tail

def multiplicity(a):
    remaining = sum(a)
    ways = 1
    for count in a:
        ways *= comb(remaining, count)
        remaining -= count
    return ways

def anchored_sign(triple):
    # With anchor 0, the positive triples correspond to edges of a five-cycle.
    from_anchor = lambda j, k: 1 if (j-k) % 5 in (1, 4) else -1
    if 0 in triple:
        return from_anchor(triple[1], triple[2])
    return prod(from_anchor(i,j) for i,j in combinations(triple,2))

def cube_sign(triple):
    if len({i//2 for i in triple}) != 3:
        return 0
    return (-1)**sum(i % 2 for i in triple)

def interpolate(points):
    coefficients = [Fraction(0)]*len(points)
    for i,(x,y) in enumerate(points):
        poly = [Fraction(1)]
        scale = y
        for j,(t,_) in enumerate(points):
            if j == i:
                continue
            scale /= x-t
            new = [Fraction(0)]*(len(poly)+1)
            for p,v in enumerate(poly):
                new[p] -= t*v
                new[p+1] += v
            poly = new
        for p,v in enumerate(poly):
            coefficients[p] += scale*v
    return coefficients

def conditional_moments(weights,n):
    # Compute E of the degree-six Taylor polynomial of w_S/Z at delta=0.
    # At each multinomial count vector use the formal variable t with
    # coordinates 1+t*(d*n_i-N). Then substitute t=1/N after truncation.
    total = sum(weights)
    sums = [0]*M
    for a in counts(n,DIM):
        delta = [DIM*i-n for i in a]
        rows = []
        for i,j,k in TRIPLES:
            x,y,z = delta[i],delta[j],delta[k]
            rows.append((1,x+y+z,x*y+y*z+x*z,x*y*z))
        denom = [sum(w*row[j] for w,row in zip(weights, rows)) for j in range(4)]
        inverse = [1]
        for j in range(1,7):
            inverse.append(-sum(denom[r]*total**(r-1)*inverse[j-r]
                                for r in range(1,min(3,j)+1)))
        row_factor = [sum(total**r*inverse[j-r]*(n*total)**(6-j)
                          for j in range(r,7)) for r in range(4)]
        ways = multiplicity(a)
        for i,row in enumerate(rows):
            sums[i] += ways*sum(x*y for x,y in zip(row,row_factor))
    scale = DIM**n*(n*total)**6
    return [Fraction(x,scale) for x in sums]

def audit(signs,amplitude):
    h = [amplitude*x for x in signs]
    weights = [amplitude.denominator + amplitude.numerator*x for x in signs]
    require(min(weights)>0 and sum(h)==0, 'Target must be a full-support probability law')
    for i,j in combinations(range(DIM),2):
        require(sum(x for t,x in zip(TRIPLES,h) if i in t and j in t)==0,
                'Pair inclusion balance failed')
    v = sum(x*x for x in h)/M
    c = Fraction(DIM**3,M)
    moments = [conditional_moments(weights,n) for n in range(1,8)]
    coefficients = []
    for i,x in enumerate(h):
        # A centered joint moment of degree j <= 6 is a polynomial in 1/N
        # of degree <= j-1. Six nodes determine it; the seventh is held out.
        coef = interpolate([(Fraction(1,n),moments[n-1][i]) for n in range(1,7)])
        require(sum(z*Fraction(1,7)**j for j,z in enumerate(coef))==moments[6][i],
                'Held-out exact quadrature disagrees')
        require(coef[:4]==[1,0,0,c*(v-x)],'Marginal coefficient mismatch')
        coefficients.append(coef[3])
    kl = sum(Fraction(w,sum(weights))*a*a for w,a in zip(weights,coefficients))/2
    return dict(amplitude=str(amplitude),relative=sorted(set(map(str,coefficients))),
                leading_KL=str(kl),targets_checked=len(weights))

def field_example(signs):
    with localcontext() as ctx:
        ctx.prec=60
        u=1/Decimal(5).sqrt()
        plus=(1+u)/2
        records=[]
        for n in (3,6,12):
            success=0
            pos=Decimal(0)
            for a in counts(n,DIM):
                weights=[prod(a[i] for i in s) for s in TRIPLES]
                unsigned=sum(weights)
                if not unsigned:
                    continue
                signed=sum(w*s for w,s in zip(weights,signs))
                ways=multiplicity(a)
                success+=ways
                pos+=ways*(unsigned+signed)*(1+u)/(2*(unsigned+signed*u))
            pos/=success
            require(0<pos<plus,'Wrong sign of finite-pool bias')
            if n==3:
                require(abs(pos-Decimal('0.5'))<Decimal('1e-55'),'N=3 redraw')
            kl=plus*(plus/pos).ln()+(1-plus)*((1-plus)/(1-pos)).ln()
            records.append(dict(N=n,successful_ordered_pools=success,p_plus=str(pos),N6_KL=str(kl*n**6)))
        require(Fraction(54,5)**2*Fraction(1,5)*Fraction(4,5)/2==Fraction(5832,625),'Six-line limit')
        return records

if __name__=='__main__':
    signs=[anchored_sign(t) for t in TRIPLES]
    cube=[cube_sign(t) for t in TRIPLES]
    cases=[audit(signs,a) for a in [Fraction(-1,2),Fraction(0),Fraction(1,2)]]
    # The signed-design amplitude enters Z only at degree three, so w_S/Z
    # through degree six is quadratic in this amplitude. The three exact
    # interpolants verify its coefficients also for u=1/sqrt(5).
    perturbation=[x+y for x,y in zip(cube,signs)]
    cases += [audit(cube,Fraction(1,2)),audit(perturbation,Fraction(1,4))]
    bad=cube[:]
    bad[0]+=1
    bad[1]-=1
    try:
        audit(bad,Fraction(1,4))
    except ValueError as err:
        require(str(err)=='Pair inclusion balance failed','Wrong mutation failure')
    else:
        raise ValueError('Unbalanced input accepted')
    print(json.dumps(dict(cases=cases,six_line_limit='5832/625',
                          six_line_enumeration=field_example(signs),invalid_balance_rejected=True),
                     sort_keys=True,indent=2))
