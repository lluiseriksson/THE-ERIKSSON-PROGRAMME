# Right edge: exact polynomial and exponential scaling of the five families

This note fixes the normalization for the terminal G5 certificate.  It is an
exact change of variables, not an asymptotic claim.

Put

```text
delta = 1/beta,   x = lambda delta/2,   y=x^2,
rho = exp(-2 sqrt(2) beta).
```

For the five regular families in
`SURFACE-RIGHT-EDGE-DIVIDED-DIFFERENCE.md`, define

```text
U0 = rho beta^( 1/2) U,        U1 = rho beta^(-3/2) U_y,
U2 = rho beta^(-7/2) U_yy,
B0 = rho beta^(-1/2) b,        B1 = rho beta^(-5/2) b_y.
```

The powers are forced by `lambda=2 beta sqrt(y)`: a `y` derivative costs
two powers of beta.  The common exponential is forced by the two saddle
phases.  Indeed, for a shift `s`, the positive- and negative-cosine charts
have exact phase maxima

```text
max_u [sin u + cos(u+s)] = sqrt(2-2 sin s),
max_u [sin u - cos(u+s)] = sqrt(2+2 sin s).
```

For `|s|<=x`, `0<=lambda<=3/2`, and `0<delta<=1/125`, their residual
exponents relative to `2 sqrt(2) beta` are bounded in absolute value by
`lambda`.  Thus the common exponential scaling leaves only bounded factors
between `exp(-lambda)` and `exp(lambda)`; it does not create a hidden
exponential loss on either saddle.

Let

```text
s(y) = sin(x)/x,
j(y) = [sin(x)-x cos(x)]/x^3,
a = j U + 2 s U_y,
a_y = j_y U + (j+2 s_y) U_y + 2 s U_yy.
```

The scaled numerator families are exactly

```text
A0 = rho beta^(-3/2) a
   = j delta^2 U0 + 2 s U1,

A1 = rho beta^(-7/2) a_y
   = j_y delta^4 U0 + (j+2 s_y) delta^2 U1 + 2 s U2.
```

If

```text
P = a b + y(a_y b-a b_y),
P0 = rho^2 beta^(-2) P,
```

then all powers cancel before interval evaluation:

```text
P0 = A0 B0 + (lambda^2/4)(A1 B0-A0 B1),
H  = -E_t/lambda = P0/(4 B0^2).
```

Consequently the terminal certificate should enclose
`U0,U1,U2,B0,B1` directly and require `B0>0`, `P0>0`.  It must never
first form the exponentially tiny unscaled `b` or the exponentially tiny
unscaled `P`.

**Status:** exact normalization and phase geometry.  A two-saddle Arb cover
and a compatible complement bound are still required; no G5 sign claim is
made by this note alone.
