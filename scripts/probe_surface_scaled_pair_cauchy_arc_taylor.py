"""Candidate angular Taylor model for one complex Cauchy arc.

The beta Taylor remainder and mode tail are intentionally omitted; this is a
conditioning probe for preserving cancellation, not a certificate.
"""

from fractions import Fraction
from concurrent.futures import ProcessPoolExecutor, as_completed
from math import comb, factorial
import mpmath as mp

from flint import acb, arb, ctx


def bessel_jet(n, X, order):
    shifted = {k: (-X).exp()*X.bessel_i(abs(k))
               for k in range(max(0, abs(n)-order), abs(n)+order+1)}
    ijet=[]
    for q in range(order+1):
        d=sum((arb(comb(q,j))*shifted[abs(n-q+2*j)]
               for j in range(q+1)), acb(0))/arb(2)**q
        ijet.append(d/arb(factorial(q)))
    return [sum((ijet[j]*arb((-1)**(q-j))/arb(factorial(q-j))
                 for j in range(q+1)), acb(0)) for q in range(order+1)]


def coeff_jets(m, X, order):
    jm=bessel_jet(m,X,order); jl=bessel_jet(m-1,X,order); jr=bessel_jet(m+1,X,order)
    def mul(x,y): return [sum((x[j]*y[q-j] for j in range(q+1)),acb(0)) for q in range(order+1)]
    jm2=mul(jm,jm); jl2=mul(jl,jl); jr2=mul(jr,jr)
    qj=[(m-1)*jl2[j]+(m+1)*jr2[j] for j in range(order+1)]
    aj=mul(jm2,qj); bj=mul(jm2,jm2)
    return [aj[q]*arb(factorial(q)) for q in range(order+1)], [arb(m)*bj[q]*arb(factorial(q)) for q in range(order+1)]


def compose(beta_jets, z_series, order):
    out=[acb(0)]*(order+1); power=[acb(0)]*(order+1); power[0]=acb(1)
    for q in range(order+1):
        if q:
            nxt=[acb(0)]*(order+1)
            for i in range(order+1):
                for j in range(order+1-i): nxt[i+j]+=power[i]*z_series[j]
            power=nxt
        for i in range(order+1): out[i]+=beta_jets[q]/arb(factorial(q))*power[i]
    return out


def run(theta0=0, theta_radius=None, order=24):
    mp.mp.dps=180
    beta_mid=mp.mpf(1629)/16+mp.mpf(1)/32; R=mp.mpf('.1')
    if theta_radius is None: theta_radius=mp.pi/64
    X=acb(arb(mp.nstr(beta_mid+R*mp.cos(theta0),180)), arb(mp.nstr(R*mp.sin(theta0),180)))
    T=arb(mp.nstr(mp.mpf(1311)/500+mp.mpf('.0005'),180))
    M=160; aj={};bj={}
    for m in range(1,M+1): aj[m],bj[m]=coeff_jets(m,X,order)
    Wb=[acb(0)]*(order+1)
    for m in range(1,M+1):
        sm=(arb(m)*T).sin(); cm=(arb(m)*T).cos()
        for n in range(m+1,M+1):
            sn=(arb(n)*T).sin(); cn=(arb(n)*T).cos(); K=arb(m)*cm*sn-arb(n)*sm*cn
            for q in range(order+1):
                d=acb(0)
                for j in range(q+1): d+=arb(comb(q,j))*(aj[m][j]*bj[n][q-j]-aj[n][j]*bj[m][q-j])
                Wb[q]+=2*d*K
    z=[acb(0)]*(order+1)
    phase=acb(arb(mp.nstr(R*mp.cos(theta0),180)), arb(mp.nstr(R*mp.sin(theta0),180)))
    for k in range(1,order+1): z[k]=phase*(1j**k)/arb(factorial(k))
    series=compose(Wb,z,order)
    H=arb(mp.nstr(theta_radius,180))
    h_interval=H*arb("0 +/- 1")
    value=acb(0); hp=arb(1)
    for q in range(order+1): value+=series[q]*hp; hp*=h_interval
    # symmetric interval is represented by evaluating both signs through an
    # Arb hull in h; use the explicit polynomial at +/- radius as a cheap
    # diagnostic enclosure of the Taylor range.
    value2=acb(0); hp=arb(1)
    for q in range(order+1): value2+=series[q]*((-H)**q); hp*=H
    out=acb(value.real if hasattr(value,'real') else value)
    upper=float(value.abs_upper())
    print("ARC_TAYLOR theta",theta0,"radius",theta_radius,"INTERVAL",value.abs_upper().str(40),"MINUS",value2.abs_upper().str(40),flush=True)
    return upper


def worker(k):
    ctx.prec=500
    mp.mp.dps=180
    theta=2*mp.pi*(mp.mpf(k)+mp.mpf('.5'))/64
    return k,run(theta,mp.pi/64)


if __name__=='__main__':
    mp.mp.dps=180
    # Exhaustive diagnostic arc cover.  Each worker has its own Arb context;
    # this is still candidate-only because beta remainders and tails are not
    # included.
    results=[]
    with ProcessPoolExecutor(max_workers=4) as pool:
        futures=[pool.submit(worker,k) for k in range(64)]
        for future in as_completed(futures):
            results.append(future.result())
    max_upper=max(value for _,value in results)
    print("ARC_TAYLOR_ARCS",len(results),"ARC_TAYLOR_MAX_UPPER",max_upper)
    print("ARC TAYLOR PROBE ONLY; beta remainder and tails omitted")
