# C10 — Eq. (2.29) / Cammarota threshold campaign

Goal: replace `CMP116Eq229Summability` by an honest theorem-shaped threshold interface.

Proposed record:
```lean
structure CMP116Eq229CammarotaThreshold where
  alpha6_nonneg : 0 ≤ alpha6
  kappa_large : kappa0 ≤ delta*kappa
  smallness : alpha6 * rootConstant ≤ threshold
  dictionary : DFamilyMatchesCammarota DIndex DParts metric
```

First deliverable: no proof of Eq. (2.29), only the exact theorem statement and every constant slot named.
