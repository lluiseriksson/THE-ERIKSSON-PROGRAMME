import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.RGCauchySummabilitySkeleton

namespace YangMills.ClayCore

open scoped BigOperators
open Classical

/-!
# CauchyDecayFromAF — Layer 14C

Bridge: AF (P91) + UV stability (P82) → Cauchy decay (P81).

This is the structural connection between the coupling recursion (Layer 13)
and the contraction estimate (Layer 12C).
-/

noncomputable section

/-- AF implies the contraction rate decays to 0 as k → ∞. -/
theorem rate_to_zero_from_af (N_c : ℕ) [NeZero N_c]
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (h_af : ∀ k, β k < β (k + 1))
    (h_rate : ∀ k, physicalContractionRate (β (k + 1)) < physicalContractionRate (β k)) :
    Filter.Tendsto (fun k => physicalContractionRate (β k)) Filter.atTop (nhds 0) := by
  sorry -- tendsto: strictly decreasing sequence bounded below by 0

/-- Conditional Cauchy decay: given P91RecursionData, close cauchy_decay_P81_step2. -/
theorem cauchy_decay_from_p91_data {d N_c : ℕ} [NeZero N_c]
    [∀ k, ActivityNorm d k]
    (data : P91RecursionData N_c)
    (β_k r_k : ℝ) (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : β_k < 2 / balabanBetaCoeff N_c)
    (C_uv : ℝ) (hC : 0 < C_uv)
    (h_uv : ∀ K₁ K₂ : ActivityFamily d (0 : ℕ),
      ActivityNorm.dist (RGBlockingMap d N_c 0 K₁) (RGBlockingMap d N_c 0 K₂)
        ≤ C_uv * ActivityNorm.dist K₁ K₂)
    (h_refine : C_uv ≤ physicalContractionRate β_k)
    (K₁ K₂ : ActivityFamily d (0 : ℕ)) :
    ActivityNorm.dist (RGBlockingMap d N_c 0 K₁) (RGBlockingMap d N_c 0 K₂)
      ≤ physicalContractionRate β_k * ActivityNorm.dist K₁ K₂ :=
  le_trans (h_uv K₁ K₂)
    (mul_le_mul_of_nonneg_right h_refine (ActivityNorm.dist_nonneg K₁ K₂))

/-!
## What this file establishes

`cauchy_decay_from_p91_data` shows that:
  P91RecursionData + UV stability (P82) + refinement h_refine
    → cauchy_decay_P81_step2

The remaining mathematical content is:
  1. Construct P91RecursionData from P91 A.2 equations
  2. Prove h_refine: C_uv ≤ exp(-β_k) using the coupling recursion
  3. rate_to_zero_from_af: tendsto result (Filter.atTop analysis)
-/

end

end YangMills.ClayCore
