# Surface S1/S2 delta-eight positive campaign — pre-registration

**Registered:** 2026-07-28, before any production unit

**State:** `DESIGN_GATE`; no K2, K4, S1''', S2''', G1, G2, G6, or
Surface Theorem promotion

## Fixed parameter domain

The campaign covers only

```text
t = 29/10,
delta in [61/2000, 1/15].
```

The born delta partition consists of

```text
[k/2000,(k+1)/2000],  k=61,...,132,
[133/2000,1/15].
```

There are exactly 73 positive, strictly ordered boxes.  The analytic
`[0,61/2000]` K2 patch and the K4 nonlocal completion are separate
obligations.

## Frozen arithmetic

Every unit uses:

```text
python-flint Arb precision  180 bits
workers                      4
spatial mesh power           3/2
```

The row partition and reduction order are deterministic.

## Frozen S1 configuration

For all 73 boxes:

```text
center grid       16 x 16
order-8 grid       4 x 4
```

All seven half-second enclosures and their literal single-box budget
fractions are printed.  Only their additive sums over all 73 boxes can pass
or fail the positive S1''' segment.

## Frozen S2 configuration

```text
delta_lo < 79/2000:
  center grid     48 x 48
otherwise:
  center grid     32 x 32
all boxes:
  order-8 grid     8 x 8
```

The quotient gauge is fixed before production by piecewise-linear
interpolation of the following design knots.  Each row stores the normalized
Taylor coefficients `(q0,q1,q2)`:

```text
delta=31/1000:
  -0.02558658084315849853267816364585336264690
  -0.8217654614598047044505896807742706192525
   0.1166008547158716583502361174913758031124
delta=1/25:
  -0.03297281690292861396976596958184651862485
  -0.8195768679837442914121064889386895127998
   0.1318725073690613039813660263094183244174
delta=1/20:
  -0.041153388497690248593365930
  -0.8162559803363880870511532
   0.2171657204568843395206
delta=1/15:
  -0.054668221249241399411735314
  -0.8033617852942335869159901
   0.6029338320739366303786
```

Centers below the first knot use the first row.  This calibration cannot
change `Y`: it subtracts the same exact scalar series from both numerator
moments before the determinant is assembled.

The S2 single-box fraction is

```text
15 * (2 |half Y'' enclosure|) * W_i
--------------------------------------
Theta3(c) * delta_final
```

where `delta_final=1/15`, `c=cos(29/40)`, and
`W_i=delta_final*(hi-lo)-(hi^2-lo^2)/2`.

## Evidence and terminal predicates

Each transcript must print:

- source commit, Python/python-flint versions, Arb precision;
- hashes of every repository Python module loaded by the unit;
- the exact born box and frozen grids;
- all half-second enclosures and fractions;
- a nonzero exit on any nonfinite value or necessary local fraction
  `>=1`.

Production and replay must contain all 73 units for each judge.  A separate
validator must reject missing, duplicated, overlapping, reordered,
hash-drifting, or numerically unequal units and must sum the fractions with
outward-rounded Arb arithmetic.  Promotion requires every global sum to
have strict upper endpoint below one.

Even a complete positive campaign does not cover `[0,61/2000]`, the K4
completion, or any non-stress `t`; it cannot by itself promote a theorem
gate.
