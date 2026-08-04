# Scaled right edge: the algebraic zero face

## Scope

This note identifies and proves the sign of the only possible `delta=0`
face of the pre-registered scaled right-edge problem.  It is an exact
algebraic consequence of the already extracted main- and mirror-chart
coefficients.  It is **not yet the analytic zero-face certificate**: a
uniform, outward-rounded remainder still has to justify passage from the
finite-`delta` integrals to these coefficients.

Put

```text
delta = 1/beta,       t = pi-lambda*delta,
r = 1/sqrt(2),        q = exp(-sqrt(2)*lambda),
L = (sqrt(2*pi)/4) r^(-5/2).
```

Here the cascade variables are `c=cos(t/4)` and `s=sin(t/4)`, so both tend
to `r`.  The exact mirror suppression is

```text
exp(-4 beta (c-s)) -> q.
```

## Coefficient assembly

Use moment units in which

```text
M_D = beta^(3/2) exp(-4 beta c) mu_D,
M_F = beta^(5/2) exp(-4 beta c) mu_F.
```

The existing main/mirror extractions give the following limiting pieces.

```text
main M_D                 ->  2 L
mirror M_D               -> -2 L q
main M_F                 -> -sqrt(2) L
beta*(mirror leading M_F)->  2 lambda L q
mirror next M_F          ->  sqrt(2) L q.
```

The last equality is not a numerical fit.  At `s=r`, the extracted exact
coefficient

```text
sqrt(2)*sqrt(pi)*(46*s^4-23*s^2+4)/(32*s^(11/2))
```

equals `sqrt(2)*L`.  The leading mirror term is the same-order contribution
because `C=cos(t/2)=sin(lambda/(2 beta))` and hence `beta*C -> lambda/2`.
Discarding either mirror contribution gives the wrong zero face.

Since `E=C+mu_F/mu_D` and `beta*C -> lambda/2`, the assembled candidate is

```text
Q_0(lambda)
 = lambda/2 + [-sqrt(2)+q*(2 lambda+sqrt(2))]/[2*(1-q)]
 = (lambda/2) coth(lambda/sqrt(2)) - 1/sqrt(2).
```

## Strict sign

Let `x=lambda/sqrt(2)`.  Direct differentiation gives

```text
H_0(lambda) = Q_0'(lambda)/lambda
 = [sinh(x) cosh(x)-x]/[2 lambda sinh(x)^2].
```

For `x>0`,

```text
d/dx [sinh(x)cosh(x)-x] = 2 sinh(x)^2 > 0,
```

and the bracket vanishes at zero.  Thus `H_0(lambda)>0` for every
`lambda>0`, in particular on `(0,3/2]`.  Its removable value is

```text
H_0(0)=1/(3 sqrt(2)).
```

This leaves a quantitatively favourable face (approximately `0.20528` at
`lambda=3/2`), but that decimal is diagnostic only.

There is also a certified rational floor on the whole face:

```text
H_0(lambda) > 1/5,       0 <= lambda <= 3/2.
```

Indeed, apart from a positive factor, the derivative of `H_0` has
numerator

```text
N(x)=2 x^2 cosh(x)-x sinh(x)-sinh(x)^2 cosh(x).
```

Using `sinh(x)^2 cosh(x)=(cosh(3x)-cosh(x))/4`, the coefficient of
`x^(2n)/(2n)!` in `N` is

```text
8 n^2-6 n-(9^n-1)/4.
```

It vanishes for `n=1,2` and is negative for every `n>=3`.  For the last
claim set `D_n=9^n-1-(32n^2-24n)`: `D_3=512` and
`D_(n+1)-9D_n=256n(n-1)>0`.  Hence `H_0` is strictly decreasing.  A
single outward-rounded Arb evaluation at `lambda=3/2` proves
`H_0(3/2)>1/5`; this endpoint comparison is part of the executable audit.

## What remains before promotion

The G5 half-line certificate still owes a uniform theorem of the form

```text
sup_{0<=lambda<=3/2} |H(lambda,delta)-H_0(lambda)| < 1/5
```

for `0<=delta<=1/125`.  The proof must use the shifted-correlation integral, keep both
saddles, remove the `lambda=0` zero before division, and cover the whole
rectangle by exact adjacent interval boxes.  Until that is done this note
closes the **algebra and sign of the proposed zero face only**; G5 remains
open.
