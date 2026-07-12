# Surface right-edge certificate: pre-registration

## Frozen target

For each declared compact beta interval, certify

```text
W(t,beta) < 0,
pi - 3/(2 beta) <= t < pi.
```

The computation works with `d = pi-t` and the analytic quotient
`W(pi-d,beta)/d^3`.  It must never divide an interval containing zero.
The exact order-three zero at `d=0` is removed coefficientwise from the
Fourier series before interval evaluation.

## Trust and coverage contract

1. Bessel coefficients and all beta derivatives use the positive-series
   Arb enclosures and geometric tails of the compact bulk certificate.
2. Values of every trigonometric derivative at `t=pi` are formed exactly
   from parity (`sin(m*pi)=0`, `cos(m*pi)=(-1)^m`); no floating
   approximation to pi is admitted in the normalized lane.
3. A beta box `[b0,b1]` covers the superset
   `0 < d <= 3/(2 b0)`, hence contains the moving wedge for every beta in
   that box.
4. Both beta and `d` coverage must be contiguous.  A terminal claim needs
   a transcript, immutable script/dependency hashes, environment versions,
   a run manifest, and an executable validator.
5. A finite compact run closes only the stated beta interval.  It does not
   supply `C_quad`, the large-beta prefactor bound, or the global G5 gate.

## Failure rule

Any indeterminate terminal box is a failure.  Refinement may shrink beta
or `d` boxes, but may not weaken the target, omit the endpoint limit, or
replace outward-rounded intervals by point samples.

Status at registration: **DESIGN ONLY; NO RIGHT-EDGE RESULT CLAIMED.**
