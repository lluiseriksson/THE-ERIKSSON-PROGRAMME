import Mathlib
import YangMills.ClayCore.BalabanRG.BalabanCouplingRecursion

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# P91AsymptoticFreedomSkeleton — Layer 13B

Decomposes `asymptotic_freedom_implies_beta_growth` into two sub-sorrys.
Source: P91 Appendix A.2.

## Mathematical content

β_{k+1} = β_k / (1 - b₀·β_k + r_k·β_k)
         = β_k / (1 - (b₀ - r_k)·β_k)

For β_{k+1} > β_k we need the denominator d := 1 - (b₀ - r_k)·β_k ∈ (0,1).

  d < 1: since b₀ - r_k > b₀/2 > 0 and β_k ≥ 1, we get d < 1. ✓
  d > 0: need 1 > (b₀ - r_k)·β_k, i.e. β_k < 1/(b₀ - r_k). ← the real constraint

Note: asymptotic freedom holds in the weak-coupling regime where β_k is large
but β_k < 1/(b₀/2) = 2/b₀. The physical coupling g² = 1/β_k → 0 as k → ∞.

## Two sub-sorrys

  step1: denominator control — d ∈ (0,1) in the weak-coupling regime
  step2: β_{k+1} > β_k from d ∈ (0,1)
-/

noncomputable section

/-- Step 1: Denominator d = 1 - (b₀ - r_k)·β_k ∈ (0,1) in weak-coupling regime.
    Requires: β_k ∈ [1, 2/b₀) and |r_k| < b₀/2. -/
theorem denominator_in_unit_interval (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_upper : β_k < 2 / balabanBetaCoeff N_c)
    (hr : |r_k| < balabanBetaCoeff N_c / 2) :
    let d := 1 - (balabanBetaCoeff N_c - r_k) * β_k
    0 < d ∧ d < 1 := by
  sorry -- P91 A.2: denominator control in weak-coupling regime

/-- Step 2: d ∈ (0,1) implies β_{k+1} > β_k. -/
theorem beta_growth_from_denominator (β_k : ℝ) (hβ : 0 < β_k)
    (d : ℝ) (hd_pos : 0 < d) (hd_lt1 : d < 1)
    (h_eq : d = 1 - balabanBetaCoeff 1 * β_k) :
    β_k < β_k / d := by
  have : d ≠ 0 := ne_of_gt hd_pos
  rw [lt_div_iff hd_pos]
  nlinarith

/-- Structural wrapper: steps 1+2 → asymptotic freedom. 0 new sorrys. -/
theorem asymptotic_freedom_from_denominator_control (N_c : ℕ) [NeZero N_c]
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hβ_upper : β_k < 2 / balabanBetaCoeff N_c)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (h_step1 : let d := 1 - (balabanBetaCoeff N_c - r_k) * β_k
               0 < d ∧ d < 1) :
    β_k < balabanCouplingStep N_c β_k r_k := by
  unfold balabanCouplingStep
  obtain ⟨hd_pos, hd_lt1⟩ := h_step1
  have hβ_pos : 0 < β_k := by linarith
  have hden_eq : 1 - balabanBetaCoeff N_c * β_k + r_k * β_k
      = 1 - (balabanBetaCoeff N_c - r_k) * β_k := by ring
  rw [hden_eq]
  have hden_pos : 0 < 1 - (balabanBetaCoeff N_c - r_k) * β_k := hd_pos
  rw [lt_div_iff hden_pos]
  nlinarith

/-!
## Summary: P91 A.2 decomposition

Before: 1 sorry (asymptotic_freedom_implies_beta_growth)
After:  1 sorry (denominator_in_unit_interval) + step2 proved (0 sorrys)

The remaining sorry is exactly: show d ∈ (0,1) for β_k in the weak-coupling window.
This requires the quantitative coupling bound from P91 A.2 §3.
-/

end

end YangMills.ClayCore
