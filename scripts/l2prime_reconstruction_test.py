from mpmath import mp, besseli, exp, sqrt, pi, mpf, e as E
mp.dps = 40

# L2' RECONSTRUCTION from the recipe (ingredients A-E, sign discipline).
# All bounds for z >= 4, theta* = (24/z)^(1/4)  (<= pi/2 for z>=4).
# Gaussian moments over [0,inf): G_k = (2k-1)!! sqrt(pi/(2z)) / z^k
# Tail_k = int_{theta*}^inf th^{2k} e^{-z th^2/2} <= e^{-z th*^2/4} * (2k-1)!!*2^k/z^k*sqrt(pi/z)
def GT(z, th):
    fact = {0: 1, 1: 1, 2: 3, 3: 15, 4: 105}
    G = {k: fact[k]*sqrt(pi/(2*z))/z**k for k in range(5)}
    T = {k: exp(-z*th**2/4)*fact[k]*(2**k)/z**k*sqrt(pi/z) for k in range(5)}
    return G, T

def I0_bounds(z):
    th = (mpf(24)/z)**mpf('0.25')
    G, T = GT(z, th)
    mid = (pi - th)*exp(-2*z*th**2/pi**2)           # chord tail, [th*, pi]
    # upper: e^{-z(1-cos)} <= e^{-z th^2/2}(1 + z th^4/24 + (e-2) z^2 th^8/576) on [0,th*]
    up = G[0] + z*G[2]/24 + (E-2)*z**2*G[4]/576 + mid
    # lower: >= e^{-z th^2/2}(1 + z th^4/24 - z th^6/720); subtract tails from POSITIVE monomials
    lo = G[0] + z*G[2]/24 - z*G[3]/720 - T[0] - z*T[2]/24
    c = pi*exp(-z)   # bounds are for pi e^{-z} I0
    return lo/c*pi/pi, up/c  # I0 in [lo/(pi e^{-z}), up/(pi e^{-z})]

def I1_bounds(z):
    th = (mpf(24)/z)**mpf('0.25')
    G, T = GT(z, th)
    mid = (pi - th)*exp(-2*z*th**2/pi**2)  # |cos| <= 1 on [th*, pi], chord
    # integrand on [0,th*]: e^{-z(1-cos)} * cos(th), cos(th) in [1-th^2/2, 1-th^2/2+th^4/24], both >= 0
    # UPPER: (1 + z th^4/24 + (e-2)z^2 th^8/576) * (1 - th^2/2 + th^4/24)
    #   product monomials: expand; positive monomials -> extend to inf; negative -> add tail
    # P_up = 1 - th^2/2 + th^4/24 + z th^4/24 - z th^6/48 + z th^8/576 (+ cross (e-2) terms, keep positive only up to th^8)
    up = (G[0] - G[1]/2 + G[2]/24
          + z*G[2]/24 - z*G[3]/48 + z*G[4]/576
          + (E-2)*z**2*G[4]/576            # times (1 - ...) <= 1 for upper: keep leading
          + T[1]/2 + z*T[3]/48             # tails ADDED for negative monomials
          + mid)
    # LOWER: (1 + z th^4/24 - z th^6/720) * (1 - th^2/2) >= ... expand:
    # = 1 - th^2/2 + z th^4/24 - z th^6/48 - z th^6/720 + z th^8/1440
    #   (drop the last positive term for a valid lower bound; subtract tails from positive monomials)
    lo = (G[0] - G[1]/2 + z*G[2]/24 - z*G[3]/48 - z*G[3]/720
          - T[0] - z*T[2]/24
          - mid)  # SIGN AUDIT FIX: [th*, pi] has cos(th) < 0 past pi/2;
                  # int_{th*}^pi e^{-z(1-cos th)} cos th dth >= -(pi-th*)e^{-2z th*^2/pi^2}
                  # (second voice's catch: dropping this region was a logical
                  # omission shared by both independent implementations)
    c = pi*exp(-z)
    return lo/c, up/c

print("VALIDITY sweep + second-order windows (true coeffs: I0 -> 9/128 = %.5f, I1 -> -15/128 = %.5f)" % (9/128, -15/128))
print(" z     I0 ok   I1 ok    z^2*(I0 window around 1+1/(8z))      z^2*(I1 window around 1-3/(8z))")
ok_all = True
for zz in [4, 6, 10, 20, 40, 80, 160, 320, 640]:
    z = mpf(zz)
    lo0, up0 = I0_bounds(z); lo1, up1 = I1_bounds(z)
    I0 = besseli(0, z); I1 = besseli(1, z)
    ok0 = lo0 <= I0 <= up0; ok1 = lo1 <= I1 <= up1
    ok_all = ok_all and ok0 and ok1
    nrm = sqrt(2*pi*z)*exp(-z)
    w0lo = z**2*(lo0*nrm - 1 - 1/(8*z)); w0up = z**2*(up0*nrm - 1 - 1/(8*z))
    w1lo = z**2*(lo1*nrm - 1 + 3/(8*z)); w1up = z**2*(up1*nrm - 1 + 3/(8*z))
    in0 = w0lo <= mpf(9)/128 <= w0up; in1 = w1lo <= mpf(-15)/128 <= w1up
    print("%4d   %s   %s    [%8s, %8s] contains: %s    [%8s, %8s] contains: %s" %
          (zz, ok0, ok1, mp.nstr(w0lo,3), mp.nstr(w0up,3), in0, mp.nstr(w1lo,3), mp.nstr(w1up,3), in1))
print("ALL BOUNDS VALID:", ok_all)

# fine validity sweep
bad = 0
z = mpf(4)
while z <= 100:
    lo0, up0 = I0_bounds(z); lo1, up1 = I1_bounds(z)
    if not (lo0 <= besseli(0,z) <= up0 and lo1 <= besseli(1,z) <= up1):
        bad += 1; print("VIOLATION at z =", z)
    z += mpf('0.5')
print("fine sweep [4,100] violations:", bad)
