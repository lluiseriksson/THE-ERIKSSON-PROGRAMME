# K2 positive-lane production contract

**Registered:** 2026-07-12, before any exhaustive positive-lane run  
**State:** `STRESS_TERMINAL_PASS`; `COVERAGE_NOT_STARTED`; `G2_OPEN`

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

## Uniform sixth-coefficient shortcut

The same registered inequality admits a stronger coefficient-level proof.
After the exact head through degree five has been removed, Taylor's theorem
gives

```text
|R(delta,t)| <= C6(t) delta^6.
```

Accordingly, before any exhaustive result is observed, the production driver
may first try to prove on each born `t` box that the nominal whole-parameter
sixth coefficient plus the order-six Bessel coefficient is strictly below
`150000`.  A coefficient bound proved on a delta superset is a common analytic
lemma applied separately to every contained birth; it is not a merged terminal
box, and the final coverage table must still list every delta birth.

The fixed delta-superset ladder is

```text
[1/1000,1/20]
    -> [0.001,0.002], [0.002,0.004], [0.004,0.008],
       [0.008,0.016], [0.016,0.032], [0.032,0.050].
```

The full interval is attempted first.  If it fails, all six listed macroboxes
are used; no data-dependent macro boundary is allowed.  If one macrobox fails
at spatial grid 32, its constituent born delta boxes revert to the per-box
accounting above.  The endpoint `[0,1/1000]` remains owned by the independent
regular certificate and is never inferred from this shortcut.

## Promotion boundary

The stress-box terminal run may certify only its one born descendant.  G2 can
move only after an exhaustive transcript proves adjacency and coverage of all
49 positive delta births and all ordered `t` births, every row has a strictly
positive terminal margin, the endpoint certificate remains valid, and an
executable validator checks the union and provenance.

## First terminal result

The last half of the last delta birth at the registered stress `t` birth,

```text
delta in [0.0495,0.05],   t in [2.9,2.92],
```

passes with total `0.000888623629659`, budget `0.00220659410016`, and
strict margin `0.00131797047050`.  The run separately reports 1,024 centre
cells, 64 whole-`t` cells, 64 whole-`(delta,t)` cells, `KD>1.9393`, delta-tail
charge `3.12e-8`, and companion charge `5.04e-5`.  Transcript and dependencies
are owned by manifest
`surface-remainder-positive-stress-20260712T182652Z`; the executable transcript
validator checks hashes, counts, positivity, margin, verdict, and one-box
scope.  This result validates the terminal accounting but does not imply any
unrun birth.
