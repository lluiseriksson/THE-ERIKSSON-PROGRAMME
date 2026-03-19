import Mathlib
import YangMills.ClayCore.BalabanRG.P91RecursionData
import YangMills.ClayCore.BalabanRG.P91BetaDriftClosed

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter

/-!
# P91BetaDivergence — Layer 14D

β_k → +∞ (via P91BetaDriftClosed) → exp(-β_k) → 0.
0 sorrys. 0 axioms. All data-driven.
-/

noncomputable section

/-- Pure analysis: exp(-β_k) → 0 when β_k → +∞. 0 sorrys. -/
theorem rate_to_zero_of_beta_tendsto_top
    (β : ℕ → ℝ) (hβ : Tendsto β atTop atTop) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  show Tendsto (fun k => Real.exp (-(β k))) atTop (nhds 0)
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hβ

/-- Full chain: data → β diverges → rate → 0. 0 sorrys. -/
theorem rate_to_zero_from_p91_data (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_upper : ∀ k, β k < 2 / balabanBetaCoeff N_c) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) :=
  rate_to_zero_of_beta_tendsto_top β
    (beta_tendsto_top_from_data_closed N_c data β r hβ0 hstep hr hβ_upper)

end

end YangMills.ClayCore
