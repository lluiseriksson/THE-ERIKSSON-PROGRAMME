import Mathlib
import YangMills.ClayCore.BalabanRG.CauchyDecayFromAF
import YangMills.ClayCore.BalabanRG.BalabanCouplingRecursionWindow
import YangMills.ClayCore.BalabanRG.P91WindowFromRecursion

namespace YangMills.ClayCore

open scoped BigOperators
open Classical Filter
noncomputable section

/-!
# CauchyDecayFromAFWindow

First downstream consumer of the analytic correction proved in
`BalabanCouplingRecursionWindow.lean`.

This file does not introduce a new hub.
It converts the proved multiplicative weak-coupling window

  β * (3 * b₀) < 2

into the older explicit upper-bound interface

  β < 2 / b₀

still consumed by `CauchyDecayFromAF.lean`.
-/

theorem beta_upper_of_window_mul
    (N_c : ℕ) [NeZero N_c] (β_k : ℝ)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    β_k < 2 / balabanBetaCoeff N_c := by
  by_cases hβ_pos : 0 < β_k
  · have hscaled : β_k * balabanBetaCoeff N_c < (2 : ℝ) / 3 := by
      nlinarith [hβ_window_mul]
    have hprod' : β_k * balabanBetaCoeff N_c < 1 := by
      linarith
    have hprod : β_k * (balabanBetaCoeff N_c + |(0 : ℝ)|) < 1 := by
      simpa using hprod'
    have hwindow' :
        β_k < 1 / (balabanBetaCoeff N_c + |(0 : ℝ)|) := by
      exact window_from_product_small N_c β_k 0 hβ_pos hprod
    have hwindow : β_k < 1 / balabanBetaCoeff N_c := by
      simpa using hwindow'
    have hb : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
    have htwo_eq :
        (2 : ℝ) / balabanBetaCoeff N_c
          = 1 / balabanBetaCoeff N_c + 1 / balabanBetaCoeff N_c := by
      field_simp [ne_of_gt hb]
      norm_num
    have hone_two : 1 / balabanBetaCoeff N_c < 2 / balabanBetaCoeff N_c := by
      rw [htwo_eq]
      have hpos : 0 < 1 / balabanBetaCoeff N_c := by
        positivity
      linarith
    exact lt_trans hwindow hone_two
  · have hβ_nonpos : β_k ≤ 0 := le_of_not_gt hβ_pos
    have hb : 0 < balabanBetaCoeff N_c := balabanBetaCoeff_pos N_c
    have htarget_pos : 0 < 2 / balabanBetaCoeff N_c := by
      positivity
    linarith

/-- AF implies rate decays to 0, now consuming the multiplicative weak-coupling window
proved in `BalabanCouplingRecursionWindow.lean`. -/
theorem rate_to_zero_from_af_in_window_mul
    (N_c : ℕ) [NeZero N_c]
    (data : P91RecursionData N_c)
    (β : ℕ → ℝ) (r : ℕ → ℝ)
    (hβ0 : 1 ≤ β 0)
    (hstep : ∀ k, β (k + 1) = balabanCouplingStep N_c (β k) (r k))
    (hr : ∀ k, |r k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : ∀ k, β k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2) :
    Tendsto (fun k => physicalContractionRate (β k)) atTop (nhds 0) := by
  exact
    rate_to_zero_from_af N_c data β r hβ0 hstep hr
      (fun k => beta_upper_of_window_mul N_c (β k) (hβ_window_mul k))

/-- Conditional Cauchy decay at scale 0, now consuming the multiplicative weak-coupling
window proved in `BalabanCouplingRecursionWindow.lean`. -/
theorem cauchy_decay_from_p91_data_in_window_mul
    {d N_c : ℕ} [NeZero N_c] [∀ k, ActivityNorm d k]
    (data : P91RecursionData N_c)
    (β_k r_k : ℝ)
    (hβ : 1 ≤ β_k)
    (hr : |r_k| < balabanBetaCoeff N_c / 2)
    (hβ_window_mul : β_k * ((3 : ℝ) * balabanBetaCoeff N_c) < 2)
    (C_uv : ℝ) (hC : 0 < C_uv)
    (h_uv : ∀ K₁ K₂ : ActivityFamily d (0 : ℕ),
      ActivityNorm.dist (RGBlockingMap d N_c 0 K₁) (RGBlockingMap d N_c 0 K₂)
        ≤ C_uv * ActivityNorm.dist K₁ K₂)
    (h_refine : C_uv ≤ physicalContractionRate β_k)
    (K₁ K₂ : ActivityFamily d (0 : ℕ)) :
    ActivityNorm.dist (RGBlockingMap d N_c 0 K₁) (RGBlockingMap d N_c 0 K₂)
      ≤ physicalContractionRate β_k * ActivityNorm.dist K₁ K₂ := by
  exact
    cauchy_decay_from_p91_data data β_k r_k hβ hr
      (beta_upper_of_window_mul N_c β_k hβ_window_mul)
      C_uv hC h_uv h_refine K₁ K₂

end

end YangMills.ClayCore
