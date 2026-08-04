# Exact shifted-correlation reduction at the right edge

**State:** exact identity.  This removes the alternating cancellation from
the proposed G5 radius certificate, but no sign is claimed here.

Put

```text
h_n = I_n(beta) I_(n+1)(beta),
g(u) = (1/2) I_1(2 beta cos u)
     = sum_(n>=0) h_n cos((2n+1)u),
S(x) = (2/pi) integral_0^pi g(pi/2-u) g(u-x) du.
```

Odd-frequency orthogonality and
`cos((2n+1)(pi/2-u))=(-1)^n sin((2n+1)u)` give the exact diagonalization

```text
S(x) = sum_(n>=0) (-1)^n h_n^2 sin((2n+1)x).
```

The coefficient definition of `F_A` can be shifted without a boundary
term:

```text
a_m = (m-1)h_(m-1)^2 + (m+1)h_m^2,
F_A(pi-d)
 = sum_(n>=0) (-1)^n h_n^2
     [n sin((n+1)d) - (n+1)sin(nd)].
```

For `k=2n+1` and `x=d/2`, the bracket is identically

```text
k sin(x) cos(kx) - cos(x) sin(kx).
```

Therefore

```text
F_A(pi-d) = sin(d/2) S'(d/2) - cos(d/2) S(d/2).       (A)
```

All exchanges are justified by the super-exponential Bessel coefficient
decay.  Identity (A) is a cancellation-preserving one-dimensional formula
for the full numerator, not an asymptotic expansion.

For the denominator, with `p_m=I_m(beta)^2`, define

```text
R(d) = sum_(m>=1) (-1)^m p_m^2 cos(md).
```

Then direct differentiation gives

```text
F_B(pi-d) = R'(d).                                      (B)
```

Equivalently, (B) is the derivative of the shifted circle convolution
already used in the second proof of denominator positivity.

Together,

```text
E(pi-d) = [sin(d/2)S'(d/2)-cos(d/2)S(d/2)] / [2R'(d)].
```

This is the preferred next engine for G5.  It keeps both mirror saddles in
the same one-dimensional integral and avoids the exponentially ill-
conditioned alternating Fourier sum.  The remaining work is an outward-
rounded scaled enclosure of the derivative of this quotient for
`lambda=beta*d in [0,3/2]`, with `delta=1/beta in [0,1/125]`; the exact
`c3>0` half-line lemma supplies the removable `lambda=0` endpoint.
