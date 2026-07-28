# Surface S2 delta-eight / spatial-five design

**Registered:** 2026-07-28

**State:** `DESIGN_ONLY`; no S2''', K4, G1, G2, or Surface Theorem
promotion

This note records the first interval architecture that closes a nontrivial
positive-delta box for the literal main-saddle quotient carrier.  It does
not replace the pre-registered terminal gates in
`SURFACE-REMAINDER-PREREG.md`.

## Target

For the normalized main-saddle carrier

```text
Y(delta) =
  4 delta^(-4) (K_D H_DF - K_F H_DD) / K_D^2,
```

the literal S2''' contribution is controlled by positive-delta boxes for
`Y''`.  The full judge also requires its weighted delta sum and a separate
analytic `[0,delta_*]` K2 patch.

## Exact architecture

The implementation in
`scripts/surface_remainder_s2_delta8_exact.py` uses:

1. the exact Laurent recurrence for derivatives of
   `A(z)=exp(-z) I_1(z)/z` and
   `B(z)=exp(-z)(I_0(z)-I_1(z)/z)/z`;
2. endpoint hulls justified by complete monotonicity, with a loud `z>4`
   domain gate;
3. total spatial Taylor degree four, with every total-degree-five term
   charged as an interval remainder;
4. a normalized delta Taylor series through order eight;
5. the exact factored phase
   `beta * (2 radius - 4 cos(t))`, which preserves the common
   `beta=1/delta` dependency on a delta box;
6. positive, born-ordered spatial meshes and deterministic row reduction.

The scaled-Bessel recurrence needs derivatives through order thirteen:
eight delta orders plus five spatial orders.  The tests compare all orders
zero through thirteen with independent multiprecision differentiation.

## Why order eight is sufficient

Let `c_n=Y^(n)(c)/n!`, `h=delta-c`, and `|h|<=rho`.  Taylor's theorem
applied directly to `Y''/2` gives

```text
Y''(c+h)/2
  = sum_(n=2)^7 [n(n-1)/2] c_n h^(n-2)
    + 28 [Y^(8)(xi)/8!] h^6
```

for some `xi` between `c` and `c+h`.  Hence no ninth derivative is
required.  The interval-base order-eight coefficient must enclose
`Y^(8)(x)/8!` for every `x` in the complete delta box; it is not
interchangeable with a point coefficient at the center.

The code therefore computes:

- coefficients zero through seven on the center fiber with the fine
  spatial grid; and
- coefficient eight on the whole delta box with a separate remainder
  grid.

It then charges

```text
28 * sup_box |coefficient_8| * rho^6.
```

## First closed design box

At the registered stress value `t=2.9`, the box

```text
delta in [0.0495, 0.05]
center grid       48 x 48
remainder grid     8 x 8
precision          180 bits
```

returned an enclosure for `Y''/2` with absolute upper bound
`6.30514`.  This is a strict local enclosure, not a global S2'''
certificate.

The early conditioning bottleneck was then rerun with the nonuniform
`p=3/2` mesh:

```text
delta in [0.0305, 0.031]
center grid       48 x 48
remainder grid     8 x 8
precision          180 bits
|Y''/2| upper       9.571540213673321
```

Thus the first positive box also closes locally.  At the intermediate box
`[0.0395,0.04]`, a `32 x 32` center mesh and `8 x 8` remainder mesh with
the same power and precision gave `|Y''/2| <= 9.268533597926891`.
These values support a tiered production grid; they do not determine or
pass the global weighted sum.

## Executable checks

```text
python -m pytest -q \
  tests/test_surface_remainder_s2_delta8_exact.py \
  tests/test_surface_remainder_s2_spatial5_exact.py
```

The current suite checks:

- normalized delta-jet algebra and factorial conventions;
- the A/B derivative recurrence against independent differentiation;
- overlap with the earlier exact raw-jet implementation;
- delta integrand coefficients zero through eight against independent
  differentiation;
- the factored phase identity;
- complete-monotonicity endpoint orientation;
- positive and strictly ordered spatial nodes.

## Promotion gates still open

Before this design can carry theorem weight:

1. freeze the complete positive delta partition, grids, mesh powers,
   calibration rule, precision, and worker count before the production
   batch;
2. produce independent production and replay transcripts with script
   hashes and dependency versions;
3. sum the literal weighted S2''' fractions over the full partition;
4. construct and certify the corresponding seven-carrier S1''' / K4
   judge;
5. prove the separate analytic K2 patch from `delta=0` to the first
   positive box;
6. audit every denominator away from zero and every interval inclusion;
7. promote G1/G2 only after all terminal predicates pass.

Two attempted Fable 5 High audits on 2026-07-28 expired without returning
a result.  No Fable conclusion is used by this design record.
