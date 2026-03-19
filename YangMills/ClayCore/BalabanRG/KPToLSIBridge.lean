import Mathlib
import YangMills.ClayCore.BalabanRG.PolymerLogLowerBound

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# KPToLSIBridge — Layer 5 (Bridge)

This file connects the finite KP polymer bounds (Layers 0–4C) to the
`balaban_rg_uniform_lsi` axiom in the main P8 architecture.

## What the Clay Core has proved (0 sorrys, 0 axioms)

  KPOnGamma Gamma K a
    → CompatibleFamilyMajorant Gamma K (exp(B) - 1)         [KPBudgetBridge]
    → SmallActivityBudget Gamma K (exp(B) - 1)              [KPConsequences]
    → |polymerPartitionFunction Gamma K - 1| ≤ exp(B) - 1  [KPConsequences]
    → 0 < polymerPartitionFunction Gamma K                  [PolymerLogBound]
    → log Z ≤ exp(B) - 1                                   [PolymerLogBound]
    → log Z ≥ -t/(1-t)   (t = exp(B)-1)                   [PolymerLogLowerBound]
    → |log Z| ≤ 2t       (when t ≤ 1/2)                   [PolymerLogLowerBound]

## The remaining gap: balaban_rg_uniform_lsi

The uniform LSI for SU(N) Gibbs measures requires:
  * The polymer free-energy bound above (mechanized in Layers 0–4C)
  * A multi-scale RG argument (Balaban 1982–88 papers, E26 paper series)
  * Uniform control of the Dirichlet form across scales

This bridge file states the key consequence theorem that would follow
from `balaban_rg_uniform_lsi` + the Clay Core bounds.
-/

noncomputable section

/-! ## Bridge statement: KP finite bound → free-energy control ready for LSI -/

/-- The polymer free-energy (log Z) is uniformly bounded by the KP budget.
    This is the key input for the Balaban RG uniform LSI argument. -/
theorem kpOnGamma_log_free_energy_bound {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hsmall : Real.exp (theoreticalBudget Gamma K a) - 1 ≤ 1/2) :
    |Real.log (polymerPartitionFunction Gamma K)|
      ≤ 2 * (Real.exp (theoreticalBudget Gamma K a) - 1) :=
  log_polymerPartitionFunction_abs_le Gamma K a ha hKP hsmall

/-- Positivity of Z is unconditional once KP holds with budget < log 2. -/
theorem kpOnGamma_partition_function_pos {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    0 < polymerPartitionFunction Gamma K :=
  polymerPartitionFunction_pos_of_budget_lt_log2 Gamma K a ha hKP hb

/-! ## What balaban_rg_uniform_lsi would add

Once `balaban_rg_uniform_lsi` is discharged (via the E26 paper series),
the following chain closes:

  kpOnGamma_log_free_energy_bound
    + balaban_rg_uniform_lsi (SU(N) Gibbs LSI with constant c = c(a,d))
    → uniform LSI for effective Gibbs measure
    → spectral gap via LSItoSpectralGap (already proved in P8)
    → exponential decay of correlations
    → mass gap > 0

The remaining mathematical content is exactly the multi-scale RG
argument formalized in papers P77–P91 of the Eriksson Programme.
-/

/-- Summary theorem: the Clay Core delivers free-energy control.
    This is the formal interface between KP combinatorics and the RG analysis. -/
theorem clayCore_free_energy_ready {d : ℕ} {L : ℤ}
    (Gamma : Finset (Polymer d L)) (K : Activity d L) (a : ℝ) (ha : 0 < a)
    (hKP : KPOnGamma Gamma K a)
    (hb : theoreticalBudget Gamma K a < Real.log 2) :
    -- Z is positive (Gibbs measure is well-defined)
    0 < polymerPartitionFunction Gamma K
    ∧
    -- free energy is bounded by the KP budget
    Real.log (polymerPartitionFunction Gamma K)
      ≤ Real.exp (theoreticalBudget Gamma K a) - 1 := by
  constructor
  · exact kpOnGamma_partition_function_pos Gamma K a ha hKP hb
  · exact log_polymerPartitionFunction_le_budget_of_budget_lt_log2 Gamma K a ha hKP hb

end

end YangMills.ClayCore
