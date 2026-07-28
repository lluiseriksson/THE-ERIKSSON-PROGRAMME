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
