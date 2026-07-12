# K2 positive-lane production contract

**Registered:** 2026-07-12, before any exhaustive positive-lane run  
**State:** `STRESS_TERMINAL_RUNNING`; `COVERAGE_NOT_STARTED`; `G2_OPEN`

This record specializes the immutable born partition in
`SURFACE-REMAINDER-K2-PARTITION.md` to the repaired terminal integrator.  It
does not alter the `150000 delta^6` target in
`SURFACE-REMAINDER-R7-PREREG.md`.

## Per-box accounting

Every terminal positive box must add, before comparison with the budget,

1. the centre residual after coefficientwise subtraction of
   `T+r2 delta+...+r6 delta^5`, evaluated only through retained delta
   degrees zero through five;
2. the first three ordinary `t` derivatives at the centre, with Taylor
   weights `h`, `h^2/2`, and `h^3/6`;
3. `h^4/24` times a whole-box fourth-`t`-derivative enclosure;
4. the sixth delta-Taylor coefficient, not included in item 1, evaluated with
   the constant delta parameter ranging over the complete delta box;
5. the order-six Bessel-companion perturbation, using `KD>0` and moment
   magnitudes after undoing the exact `KF-q KD`, `HDF-q HDD` calibration.

The spatial Taylor polynomial is retained through total degree four and
integrated exactly against the affine phase.  Only total-degree-five spatial
derivatives are charged by absolute values.  All quantities are outward-rounded
Arb balls.

## Deterministic spatial refinement ladder

Each born box starts on uniform grid 8.  If the terminal margin is not
strictly positive it advances, without inspecting any alternative mesh, through

```text
8 -> 16 -> 24 -> 32.
```

The centre track alone advances on this ladder.  The whole-`t`-box and
whole-`(delta,t)` auxiliary tracks start on grid 8 and advance through the same
ladder only if their individual enclosures are non-finite or the combined
margin fails after the centre reaches grid 32.  A failure at grid 32 triggers
the already permitted bisection of that parameter box; it does not permit a
larger threshold, a widened box, or a different unregistered spatial mesh.

Every uniform grid is split into four contiguous row slices with one common
calibration.  The parent process reconstructs outward endpoint hulls and sums
the four pieces.  A grid-8 smoke reproduced the sequential five-derivative
enclosure exactly at printed precision.

## Promotion boundary

The stress-box terminal run may certify only its one born descendant.  G2 can
move only after an exhaustive transcript proves adjacency and coverage of all
49 positive delta births and all ordered `t` births, every row has a strictly
positive terminal margin, the endpoint certificate remains valid, and an
executable validator checks the union and provenance.
