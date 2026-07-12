# Surface remainder K4 fixed-domain design

**Date:** 2026-07-11
**State:** `IDENTITY_IMPLEMENTED`; `L3_POINT_SMOKE_PASS`; `K4_OPEN`

Let `D=[0,6/5]^2`, `delta_1=1/15`, and
`Q=[0,10 sqrt(delta_1)]^2`.  For every `0<delta<=delta_1`, the
support of the registered cutoff lies inside `Q`.  In one symmetry quadrant
the exact complement can therefore be written

```text
v_comp(delta) = 4 integral_Q [1_D-chi((s^2+a^2)/delta)] f_delta(s,a) ds da.
```

This is algebraically the true integral over `D` minus the localized core.
Unlike the scaled-coordinate representation, both `D` and `Q` are fixed.
There is consequently no moving-boundary term to estimate or accidentally
omit.  With `w_delta=1_D-chi_delta`, the exact differentiated integrand is

```text
(w f)'' = w f'' + 2 w' f' + w'' f.
```

The cutoff derivatives are exactly those pre-registered in
`SURFACE-REMAINDER-PREREG.md`.  The executable identity and its strict
subdivision rule are in `scripts/surface_remainder_complement.py`; fixed
physical jets for all four mirror carriers are in
`scripts/surface_remainder_carrier_jet.py` and are checked against independent
multiprecision differentiation.

This reformulation does not pass K4.  Promotion requires finite Arb integral
enclosures for the value, first, and second derivative on every delta box,
followed by the literal weighted S1'''/S2''' judges. A box crossing either
cutoff junction must subdivide before its terminal enclosure. A finite
terminal cover may use the implemented piecewise hull: the transition formula
is evaluated only on the clipped `q` interval and its derivatives are hulled
with the zero derivatives of the adjacent constant piece. Extending the
polynomial beyond `q in [0,1]` remains forbidden.

The manifested stress-point ladder contracts from grid 32 to grid 64. At
grid 64 the second-derivative coefficient enclosures include

```text
main:   muF [2e1 +/- 2.35], nuD [-0.8 +/- 0.0711], nuF [4e0 +/- 0.470]
mirror: MD  [1.1e1 +/- 0.855], MF [-6e0 +/- 0.669],
        MD2r [-3e0 +/- 0.326], MDFr [1e0 +/- 0.497].
```

These are point-smoke enclosures, not budget inequalities. Their role is to
show finiteness, expose the true order of the endpoint layer, and size the
delta partition. K4 remains open until the same machinery covers delta boxes
and the value/first/second completion derivatives enter the weighted judges.

The first literal delta-box trials locate a separate dependency obstruction.
At the exact endpoint, spatial grids 16 (core) and 16 (completion) restore
finiteness, so there is no true singularity.  On the terminal delta interval,
halving its width from `0.001` to `0.0005`, `0.00025`, and `0.000125` reduces
the most restrictive single-box `nuD` weighted-budget fractions from about
`1.064` to `0.0794`, `0.00779`, and `0.000898`.  Thus the exact Taylor weight
works near the terminal endpoint.

The same width `0.0005` is not a global partition: its `nuD` fraction is about
`22.1` at `delta=0.05`, `1494` at `delta=0.03`, and becomes unusable near
`delta=0.01`, contrary to the independently measured true profile.  The loss
comes from inserting the full delta box into a second-order jet and then
reading its second coefficient.  K4 production therefore needs a centred
delta representation with a rigorously enclosed next derivative, or an
analytic regular patch reaching far enough from zero.  Blindly shrinking
thousands of delta boxes is rejected as a completion strategy.
