# Clay Core — BalabanRG Status (v0.8.80, 2026-03-19)

**52 files · 0 errors**

## Theorems proved this session (structural, 0 sorrys each)

- `tendsto_atTop_of_linear_drift` (14E): succ_nsmul+linarith+simpa+exists_lt_nsmul
- `beta_ge_one_all` (14I): induction via one_step_beta_drift_from_controls
- `uniform_drift_from_data` (14I): positivity + linarith (0 sorrys)
- `beta_linear_drift_from_data` (14J): structural wrapper
- `beta_tendsto_top_from_data_closed` (14J): via tendsto_atTop_of_linear_drift
- `one_step_beta_drift_P91` (14H): SORRY ELIMINATED via positivity control
- `beta_step_sub_eq` (14G): exact drift identity (field_simp + ring)
- `beta_step_drift_lb` (14G): div_le_div_of_nonneg_left (0 sorrys)
- `coeff_ge_half_betaCoeff` (14H): linarith from |r_k|<b₀/2
- `denom_le_one_always` (14H): nlinarith + mul_pos

## Active P91 chain (all 0 sorrys)
```
P91DriftPositivityControl (14H)
  → P91UniformDrift (14I): beta_ge_one_all, uniform_drift_from_data
  → P91BetaDriftClosed (14J): beta_linear_drift_from_data, beta_tendsto_top_from_data_closed
  → P91BetaDivergence: rate_to_zero_of_beta_tendsto_top (0 sorrys ✅)
  → CauchyDecayFromAF: rate_to_zero_from_af (0 sorrys ✅)
```

## Remaining analytic gaps

| Sorry | File | Source |
|---|---|---|
| `large_field_decomposition_P80_step1` | P80EstimateSkeleton | P80 §4.1 |
| `large_field_exponential_suppression_P80_step2` | P80EstimateSkeleton | P80 §4.2 |
| `cauchy_decay_P81_step2` | RGCauchySummabilitySkeleton | P81 §3 |
| `beta_linear_drift_P91` | P91BetaDriftDecomposition | P91 A.2 §3 |
| `remainder_small_P91` | P91WindowFromRecursion | P91 A.2 §3 |
| `window_from_remainder` | P91WindowFromRecursion | P91 A.2 §3 |
| `window_invariant_P91` | P91WindowFromRecursion | P91 A.2 §3 |

## Notable: active path is clean
The P91 drift/divergence/rate chain has 0 sorrys in the active path.
`beta_linear_drift_P91` is only used in the legacy `P91BetaDriftDecomposition`
which is bypassed by `P91BetaDriftClosed` in the active chain.
