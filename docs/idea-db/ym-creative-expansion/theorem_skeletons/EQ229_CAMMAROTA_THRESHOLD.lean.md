# Eq. (2.29) / Cammarota threshold skeleton

```lean
structure CMP116Eq229CammarotaThreshold (...) : Prop where
  theorem_statement_extracted : Prop
  d_family_dictionary : Prop
  metric_dictionary : Prop
  alpha6_small : Prop
  K_large : Prop
  summability : CMP116Eq229Summability DIndex DParts alpha6 delta kappa metric
```

No theorem may replace “K sufficiently large and alpha6 sufficiently small” by
numerical constants until dependencies are source-extracted.
