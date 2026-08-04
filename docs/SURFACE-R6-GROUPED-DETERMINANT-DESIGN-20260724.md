# R6 grouped determinant diagnostic (2026-07-24)

The determinant was expanded over spatial groups,

```text
N = sum_(i,j) (KD_i*HDF_j - KF_i*HDD_j),
```

before forming the normalized fifth coefficient. On born box 0 at grid 64,
the grouped radii were:

```text
groups 4    Y5 radius 184697.969482421875
groups 8    Y5 radius 185089.746337890625
groups 16   Y5 radius 185251.704589843750
groups 32   Y5 radius 185682.835205078125
```

The determinant constant interval still contains zero (`B0=[+/-0.826]`) and
the grouped expansion does not contract the R6 width. This rejects the naive
finite-group double-sum implementation as a completion route. A successful
module must preserve sign information inside the carrier/envelope itself,
rather than multiplying interval group moments.

**Status:** design-only; no K2, `(H_tail)`, G2, or G6 promotion.
