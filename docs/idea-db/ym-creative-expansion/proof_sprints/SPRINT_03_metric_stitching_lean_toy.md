# Sprint 03 — Metric stitching Lean toy

Objective: prove the finite exponential extraction lemma from `d(Y) ≤ Σ d_i + (n-1)`.

Candidate statement:
```lean
theorem exp_metric_stitching_absorb
  (h : dY ≤ sumD + (n - 1)) (hb : b ≤ a) ... :
  Real.exp (-a * sumD) * Real.exp (b * (n-1)) ≤ Real.exp (-a * dY)
```

This is low-risk and can later support Appendix F / Eq. (2.37).
