# Surface S1 seven-carrier delta-eight design

**Registered:** 2026-07-28

**State:** `DESIGN_ONLY`; no K4, S1''', G1, G2, G6, or Surface Theorem
promotion

This note records the exact local-saddle successor to the historical K4
boxes that failed the literal additive judge.  The implementation is
`scripts/surface_remainder_s1_delta8_exact.py`.

## Seven carriers

At the stress value `t=2.9`, the fixed physical main and mirror quadrants
produce:

```text
main:   muF, nuD, nuF
mirror: MD, MF, MD2r, MDFr.
```

The committed budgets are, respectively,

```text
muF 26.467, nuD 0.94119, nuF 8.1751,
MD 56.801, MF 156.28, MD2r 12.577, MDFr 44.352.
```

The common exponential is evaluated with the exact factored phase on each
saddle.  No quotient or cancellation between different carriers is used.

## Architecture

The S1 lane reuses the exact order-thirteen scaled-Bessel recurrence and
complete-monotonicity endpoint hulls from the S2 lane.  For every delta
coefficient zero through eight it:

1. integrates the total spatial Taylor polynomial through degree four;
2. charges all total-degree-five terms as an outward-rounded remainder;
3. keeps the main and mirror phases separate;
4. transports the center coefficients zero through seven across the delta
   box and charges the interval-base order-eight coefficient by Taylor's
   theorem;
5. returns one half of each ordinary second derivative, matching the
   literal judge convention.

The independent TJet implementation in
`surface_remainder_centered_delta_carrier.py` is used only as a test oracle
for point coefficients zero through four.  It is not a dependency of the
new integrator.

## Design measurements

All boxes below have width `1/2000`, 180-bit Arb arithmetic, a `16 x 16`
center mesh, a `4 x 4` order-eight remainder mesh, and mesh power `p=3/2`.
The table reports the largest single-box fraction among the seven literal
S1''' budgets.

```text
delta box                 worst carrier   fraction
[0.0305,0.031]            nuD             0.0119571
[0.0495,0.05]             nuD             0.00274133
[397/6000,1/15]           nuD             0.0000673315
```

These are local design measurements, not an additive global verdict.  They
show that the new architecture avoids the interval inflation responsible
for the historical false green and that a full positive-delta batch is
computationally plausible.

## Executable checks

```text
python -m pytest -q \
  tests/test_surface_remainder_s1_delta8_exact.py \
  tests/test_surface_remainder_s2_delta8_exact.py \
  tests/test_surface_remainder_s2_spatial5_exact.py
```

The current joint suite passes 17 tests.  It includes:

- coefficient comparisons with the independent main/mirror TJet carrier;
- an order-eight comparison with direct multiprecision differentiation;
- the exact Taylor factor `28` for the half-second remainder;
- a finite two-saddle spatial cell;
- all recurrence, factorial, monotonicity, phase, and mesh checks inherited
  from the S2 lane.

## Scope still missing

This module integrates the two fixed local saddle quadrants only.  It does
not certify the nonlocal completion required by K4, the analytic
`delta=0` patch required by K2, a complete positive-delta partition, or the
additive global S1''' fractions.  Those four items must be supplied before
any ledger or manuscript promotion.
