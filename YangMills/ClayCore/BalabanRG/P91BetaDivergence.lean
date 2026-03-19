import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.P91BetaDriftDecomposition

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# P91BetaDivergence — Layer 14D

Core physical content: β_k → +∞ (AF) → exp(-β_k) → 0 (contraction).
-/

noncomputable section

/-- Core P91 A.2 §3 claim: β_k → +∞ along the recursion. 1 sorry. -/
theorem beta_tendsto_top_from_recursion_data (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    : Tendsto β atTop atTop := by
  exact beta_tendsto_top_from_drift N_c data β r hβ0 hstep hr

/-- Pure analysis: exp(-β_k) → 0 when β_k → +∞. 0 sorrys. -/
theorem rate_to_zero_of_beta_tendsto_top
    (β : ℕ → ℝ) (hβ : Tendsto β atTop atTop) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  show Tendsto (fun k => Real.exp (-(β k))) atTop (nhds 0)
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hβ

/-- Structural corollary. 0 new sorrys. -/
theorem rate_to_zero_from_p91_data (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    : Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) :=
  rate_to_zero_of_beta_tendsto_top β
    (beta_tendsto_top_from_recursion_data N_c data β r hβ0 hstep hr)

end

end YangMills.ClayCore
