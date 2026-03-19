import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.P91BetaDivergence
import YangMills.ClayCore.BalabanRG.RGCauchySummabilitySkeleton

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# CauchyDecayFromAF — Layer 14C (v0.8.81)

Bridge: P91 data → β diverges → rate → 0.
0 sorrys. Takes hβ_upper explicitly.
-/

noncomputable section

/-- AF implies rate decays to 0. 0 sorrys. -/
theorem rate_to_zero_from_af (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) :=
  rate_to_zero_from_p91_data N_c data β r hβ0 hstep hr hβ_upper

/-- Conditional Cauchy decay: given P91RecursionData → Cauchy estimate. 0 sorrys. -/
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

end

end YangMills.ClayCore
