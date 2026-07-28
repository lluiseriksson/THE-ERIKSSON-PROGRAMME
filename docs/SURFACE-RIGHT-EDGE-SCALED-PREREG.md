# Scaled right-edge half-line certificate: pre-registration

## Frozen target

Write

```text
delta = 1/beta,
d = pi-t = lambda*delta,
0 <= delta <= 1/125,
0 < lambda <= 3/2.
```

Define the removable scaled quotient

```text
Q(lambda,delta) = E(pi-lambda*delta,1/delta)/delta.
```

The certificate target is

```text
H(lambda,delta) = partial_lambda Q(lambda,delta)/lambda > 0
```

on the closed rectangle after analytic continuation to `lambda=0` and
`delta=0`.  Strict positivity of `H` implies `E'<0` throughout the moving
right edge; neither endpoint itself is claimed as an interior theorem point.

## Exact regularization

Let

```text
A(d,beta)=F_A(pi-d,beta),
B(d,beta)=F_B(pi-d,beta)>0.
```

At fixed `delta`, direct differentiation gives

```text
partial_lambda Q = [A_d B-A B_d]/(2 B^2) = -W/(4 B^2).
```

Thus the scaled target is exactly equivalent to the original Wronskian
sign.  No estimate is differentiated.

The numerator must be evaluated through the exact shifted-correlation
identity

```text
A(d)=sin(d/2)S'(d/2)-cos(d/2)S(d/2),
S(x)=(2/pi) integral_0^pi g(pi/2-u)g(u-x)du,
g(u)=I_1(2 beta cos u)/2.
```

The denominator uses the shifted convolution derivative `B(d)=R'(d)`.
Alternating Fourier summation is forbidden in the half-line lane.

## Endpoint contracts

1. `lambda=0`: remove the exact cubic zero of `A` and the linear zero of
   `B` coefficientwise before interval division.  The proved lemma
   `c3(beta)>0` for `beta>=125` is mandatory input.
2. `delta=0`: use scaled Bessel companions with inverse arguments and the
   two saddle charts.  No interval may form `exp(const/delta)` or divide by
   an interval containing zero.
3. The mirror saddle stays in the same correlation integral; it may not be
   discarded or bounded as exponentially negligible when `lambda=O(1)`.

## Trust and failure rules

* All constants, source hashes, Arb/Python versions and box endpoints must
  be printed in every production transcript.
* A design point or finite `beta` extension never closes the half-line.
* Parameter boxes must form exact adjacent unions in both `lambda` and
  `delta`, with a separate analytic zero-face certificate.
* Any nonpositive or indeterminate box is a failure.  Refinement may shrink
  boxes but may not increase `lambda_max=3/2`, omit either zero face, or
  replace outward-rounded intervals by point samples.
* The accelerated finite-beta certificate is an independent overlap audit;
  it is not a substitute for the `delta=0` face.

Status at registration: **DESIGN CONTRACT ONLY; G5 REMAINS OPEN.**
