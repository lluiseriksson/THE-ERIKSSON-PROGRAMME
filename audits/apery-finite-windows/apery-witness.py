"""Exact finite Stieltjes certificates for rational Apéry parameters."""
from functools import reduce
from math import comb, gcd
from fractions import Fraction
import json
from pathlib import Path

def require(test, msg):
    if not test:
        raise ValueError(msg)

def coefficients(k):
    return [comb(k,j)**2 * comb(k+j,j)**2 for j in range(k+1)]

def primitive(poly):
    d=reduce(gcd,poly,0)
    require(d>0,'zero polynomial')
    return [v//d for v in poly]

def point(p,q,s,limit):
    # Integer moments of u=q*t, including the strictly positive factor q**s.
    a=[sum(v*p**j*q**(k-j) for j,v in enumerate(coefficients(k))) for k in range(2*limit+s+1)]
    def inner_monomial(P,j):
        return sum(v*a[i+j+s] for i,v in enumerate(P))
    prev=[]; hprev=1; P=[1]; norms=[]
    for n in range(limit+1):
        require(all(inner_monomial(P,k)==0 for k in range(n)), 'basis orthogonality')
        last=inner_monomial(P,n); h=P[-1]*last
        if h<=0:
            require(h<0,'zero pivot; a separate certificate is needed')
            return dict(degree=n, earlier_positive=len(norms), P=P, form=h)
        norms.append(h)
        if n==limit:break
        mix=P[-1]*inner_monomial(P,n+1)+(P[-2] if n else 0)*last
        cross=prev[-1]*last if prev else 0
        nxt=[(h*hprev*(P[i-1] if i else 0)
              -mix*hprev*(P[i] if i<=n else 0)
              -cross*h*(prev[i] if i<n else 0)) for i in range(n+2)]
        prev,hprev,P=P,h,primitive(nxt)
    return dict(degree=None, earlier_positive=len(norms))

def form_coeffs(P,q,s):
    # L_x[t^s P(q*t)^2] is a polynomial in x with integer coefficients.
    n=len(P)-1; B=[0]*(2*n+s+1)
    for k in range(2*n+1):
        pk=sum(P[i]*P[k-i] for i in range(max(0,k-n),min(k,n)+1))*q**k
        for j,v in enumerate(coefficients(k+s)):B[j]+=pk*v
    return B

def bernstein_signs(B,l,r):
    # Clear denominators before testing the power coefficients of
    # (1+z)^d F((l+r*z)/(1+z)); z>=0 parametrises the entire interval.
    from math import lcm
    den=lcm(l.denominator,r.denominator); u=int(l*den);v=int(r*den);d=len(B)-1
    # Homogeneous Horner evaluation, multiplying the current polynomial by u+v*z.
    T=[B[d]];power=1
    for i in range(d-1,-1,-1):
        power*=den; m=d-i;C=B[i]*power
        T=[(u*T[k] if k<m else 0)+(v*T[k-1] if k else 0)+C*comb(m,k) for k in range(m+1)]
    return T

def validate_witness(P,p,q,s,form):
    B=form_coeffs(P,q,s);x=Fraction(p,q)
    val=sum(v*x**j for j,v in enumerate(B))
    require(val*q**s==form and form<0,'independent full quadratic form')
    # A fixed protocol, no assertion of failure outside the reported interval.
    steps=[]
    for j in range(0,41):
        rad=(1-x)/2**j; l=x-rad;r=x+rad
        T=bernstein_signs(B,l,r)
        if max(T)<0:
            steps=[str(l),str(r),j]
            break
    require(steps,'no certified radius down to the protocol limit')
    return dict(parameter=str(x),shift=s,degree=len(P)-1,scaling_q=q,coefficients_hex=[hex(v) for v in P],direct_form_hex=hex(form),interval=steps[:2],halvings=steps[2])

def main():
    rows=[];witnesses=[]
    for p,q,limit in [(1,2,9),(9,10,23),(19,20,55),(24,25,60),(39,40,76),(49,50,80)]:
        pair=[]; row=[]
        for s in (0,1):
            hit=point(p,q,s,limit)
            pair.append(hit);row.append({'shift':s,'first_negative_degree':hit['degree'],'earlier_positive':hit['earlier_positive']})
        ds=[r['degree'] for r in pair if r['degree'] is not None]
        best=min(ds) if ds else None
        for s,hit in enumerate(pair):
            if best is not None and hit['degree']==best:
                witnesses.append(validate_witness(hit['P'],p,q,s,hit['form']))
        rows.append(dict(parameter=str(Fraction(p,q)),limit=limit,first_degree=best,forms=row))
    require([r['first_degree'] for r in rows[:2]]==[8,22],'published controls')
    Path('witnesses.json').write_text(json.dumps(witnesses))
    print(json.dumps(dict(points=rows,upper_intervals=[{k:v for k,v in w.items() if k not in ('coefficients_hex','direct_form_hex')} for w in witnesses])))
if __name__=='__main__':main()