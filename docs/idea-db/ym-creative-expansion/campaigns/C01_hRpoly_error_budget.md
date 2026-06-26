# Campaign C01 — hRpoly as an explicit activity error budget

## Goal
Convert the vague physical-to-source bridge into a finite error budget:

```text
YM physical activity
  -> covariance/root localized Gaussian model
  -> CMP116 localized activity family
  -> Dimock/Appendix-F H# output
```

## Formula

```text
|H_YM#(Y)| <= |H_src#(Y)| + E_cov(Y) + E_gauss(Y) + E_support(Y) + E_jacobian(Y)
```

If every term has exponential metric decay, the minimum exponent wins.

## First Lean target

```lean
structure YMActivityErrorBudget (Y : Type*) where
  sourceAmp covAmp gaussAmp supportAmp jacAmp : ℝ
  sourceEta covEta gaussEta supportEta jacEta : ℝ

theorem activity_decay_of_source_and_budget ...
```

## Removed hypothesis if successful
Not `hRpoly` directly. It removes hidden dictionary ambiguity and splits `hRpoly` into auditable subgoals.
