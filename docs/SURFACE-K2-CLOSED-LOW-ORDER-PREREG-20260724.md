# K2 closed low-order coefficient rederivation — preregistration (2026-07-24)

This is a symbolic design brick.  It has no numerical, K2, G2, or manuscript
load until an independent interval remainder and complement-tail certificate
is added.

The script `scripts/surface_remainder_delta0_closed_low_order.py` rederives
the coefficients through order three using explicit finite polynomial
operations in `delta` (addition, multiplication, reciprocal recurrence,
binomial powers, and exponential recurrence).  It deliberately does not call
`sympy.series` or numerical quadrature.  Gaussian moments are then evaluated
exactly on the formal plane carrier, and the quotient coefficients are
assembled from the resulting rational expressions in `c=cos(t/4)`.

Acceptance gates:

1. the computed coefficients must simplify to the four registered closed
   forms `y0`, `y1`, `y2`, and `r4(c)`;
2. the formal bilinear constant `B0` must simplify identically to zero;
3. a failure is recorded and no interval or manuscript work follows.

The formal plane computation does not prove the finite spatial box, the
companion Bessel remainder, or the outer derivative tail.

The independent containment check
`scripts/validate_surface_remainder_closed_low_order_vs_interval.py` passes
for orders `0..3` of all four moments at both `t=2.90` and `t=3.13` (grid 24);
the parameterised JSON transcripts are
`scripts/validate_surface_remainder_closed_low_order_vs_interval_290_20260724.json`
and `scripts/validate_surface_remainder_closed_low_order_vs_interval_313_20260724.json`.
The intervals are intentionally wide and the result is still non-terminal.

A separate positive-polynomial Gaussian-tail design gives complement charges
between `4.7e-27` and `1.6e-24` for orders `0..4` at `t=2.90`; see
`scripts/probe_surface_remainder_closed_gaussian_tail.py` and its JSON output.
Those numbers use the midpoint `c` value and therefore are not yet a uniform
t-box certificate.  The follow-up endpoint-enclosed probe in
`docs/SURFACE-K2-UNIFORM-GAUSSIAN-TAIL-DESIGN-20260724.md` removes that
midpoint dependency for finite t-boxes, but still carries design-only status.
