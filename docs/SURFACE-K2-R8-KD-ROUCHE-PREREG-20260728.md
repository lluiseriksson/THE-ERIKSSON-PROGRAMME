# K2 degree-eight integrated-KD Rouché certificate — preregistration

**Purpose.** Prove that the fixed-square polynomial-companion `KD(delta)`
has no zero in `|delta|<=17/2000`, a missing hypothesis for Cauchy's
coefficient bound.

The run is gated on green, identical production/replay transcripts for the
degree-eight pointwise complex geometry.  Freeze:

```text
t = 29/10
rho = 17/2000
fixed square = [0,12]^2, reflected with factor 4
relative A-companion degree = 8
p-over-delta terms = 18 plus explicit tail
Arb/Acb precision = 140 bits
(spatial grid, theta arcs) = (24,32), (48,64), (96,128)
```

For each spatial cell, evaluate the interval difference between its complex
KD integrand on a full theta arc and the same integrand at `delta=0`.
After integration, accept the first level satisfying

```text
max_{|delta|=rho} |KD(delta)-KD(0)| < |KD(0)|.
```

The circle is covered by interval arcs; no sampled maximum is admissible.
Together with the separately certified pointwise holomorphy, Rouché then
gives zero integrated-KD zeros in the disk.  Exhausting the ladder is
failure.  This remains a fixed-square surrogate statement; true companions,
the exterior, and K2 remain open.

## Result

Production and replay are byte-identical.  The first level was unresolved,
as permitted; the `48 x 64` level proved

```text
|KD(0)| lower                         = 2.0481372922658920
max boundary |KD(delta)-KD(0)| upper = 1.0155682805925608
```

and hence the strict Rouché inequality.  The fixed-square degree-eight
surrogate KD has no zero in the closed disk bounded by the registered
circle.  Both transcript SHA-256 digests are
`045EAC1D5D174B51D88B09F77B9320994ADA06AD21525DD55D0518BF4F36B9EE`.

The true companion, exterior, and K2 remain open exactly as preregistered.
