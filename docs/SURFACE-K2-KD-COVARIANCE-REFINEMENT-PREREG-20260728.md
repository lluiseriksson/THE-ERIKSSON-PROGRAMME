# K2 KD-covariance refinement — preregistration

**Registered:** 2026-07-28, after grids 12 and 24 and before grid 48.

**State:** conditioning design only; no K2, K4, S1/S2, gate, or manuscript
promotion.

The exact identity under test is

```text
dP = K D dx / KD,
A = F/D,
G = ((H/K)D - 1/(4c))/delta,
Y = 4 Cov_P(A,G).
```

The delta-zero KD cell masses are integrated by the exact separated Gaussian
`erf` formula.  The centered between-cell covariance and the within-cell
first-derivative oscillation are enclosed with Arb.

The frozen refinement is:

```text
t = 29/10
delta = 0
scaled square = [0,12]^2
grid = 48 per axis
Arb precision = 140 bits
```

The design predicate is:

1. every printed quantity is finite;
2. the total KD mass has strictly positive outward lower endpoint;
3. the enclosure overlaps the exact closed form
   `(4c^2-1)/(8c^3)`;
4. the outward radius of the Y enclosure is strictly below `1`.

Failure retires blind first-derivative refinement of this representation.
Pass authorizes only a higher-spatial-order implementation.  It cannot
promote K2 because the probe omits the true Bessel companion, the exterior
tail, and every uniform positive-delta remainder.

## Post-run implementation correction

The first execution exposed a factor-of-four error in the within-cell Grüss
charge: the code divided by four after its inputs were already
center-deviation radii.  That transcript is preserved but superseded in
`INCIDENT-K2-KD-COVARIANCE-GRUSS-FACTOR-20260728.md`.  The frozen mathematical
predicate above is unchanged; the corrected implementation is rerun under
the original authoritative output filename.
