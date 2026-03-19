# Clay Core — BalabanRG Status (v0.8.55, 2026-03-19)

**10 files · 0 errors · 0 sorrys · 1 axiom remaining**

## Mechanized chain

```
KPOnGamma Gamma K a
  → CompatibleFamilyMajorant Gamma K (exp(theoreticalBudget)-1)
  → SmallActivityBudget Gamma K (exp(theoreticalBudget)-1)
  → |polymerPartitionFunction Gamma K - 1| ≤ exp(theoreticalBudget)-1
  → 0 < polymerPartitionFunction Gamma K          (when budget < log 2)
  → log Z ≤ exp(theoreticalBudget)-1
  → |log Z| ≤ 2*(exp(theoreticalBudget)-1)        (when budget ≤ log(3/2))
  → clayCore_free_energy_ready                     (KPToLSIBridge)
```

## File inventory

| File | Layer | Key theorems | Status |
|---|---|---|---|
| `BlockSpin.lean` | 0A | `LatticeSite`, `Block`, `scaleHierarchy` | ✅ |
| `FiniteBlocks.lean` | 0B | block-spin averaging, linearity | ✅ |
| `PolymerCombinatorics.lean` | 1 | `Polymer`, `KPOnGamma`, `kp_activity_bound` | ✅ |
| `PolymerPartitionFunction.lean` | 2 | `Z`, `Ztail`, `SmallActivityBudget`, `|Z-1|≤B` | ✅ |
| `KPFiniteTailBound.lean` | 3A | `KPOnGamma`, `theoreticalBudget`, `kpOnGamma_mono` | ✅ |
| `KPBudgetBridge.lean` | 3B | `kpOnGamma_implies_compatibleFamilyMajorant` | ✅ |
| `KPConsequences.lean` | 4A | `kpOnGamma_implies_abs_Z_sub_one_le`, positivity | ✅ |
| `PolymerLogBound.lean` | 4B | `0 < Z`, nonvanishing, upper log bound | ✅ |
| `PolymerLogLowerBound.lean` | 4C | `|log Z| ≤ 2t`, Mercator bound | ✅ |
| `KPToLSIBridge.lean` | 5 | `clayCore_free_energy_ready` | ✅ |

## Remaining gap

**`balaban_rg_uniform_lsi`** — the single Clay core axiom.

Claims: the SU(N) Gibbs measure at weak coupling satisfies a uniform
Log-Sobolev inequality with constant `c > 0` independent of volume.

Mathematical content: multi-scale Balaban RG argument (papers P77–P91).
Once discharged, the chain closes via `LSItoSpectralGap` (already green in P8):

```
balaban_rg_uniform_lsi
  + clayCore_free_energy_ready
  → uniform LSI for effective Gibbs measure
  → spectral gap (LSItoSpectralGap ✅)
  → exponential decay of correlations (StroockZegarlinski ✅)
  → ClayYangMillsTheorem (ErikssonBridge ✅)
```

## Key tactic lessons learned

- `positivity` cannot handle `a * X.size` without `(ha : 0 ≤ a)` explicit
- `rw [set_var]` fails after `set`; use `change` instead  
- `Finset.not_mem_erase` is a function, not a constant; use `have hne := ...`
- `Real.add_one_le_exp` gives `1 + x ≤ exp x`; orientation matters with `simpa [add_comm]`
- `linarith [hrec, hmul]` is more robust than `le_trans hrec (add_le_add_left hmul _)`
- `constructor+simpa [Real.exp_log h]` beats `change` for iff goals involving `exp`
