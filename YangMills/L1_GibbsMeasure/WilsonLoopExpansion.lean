/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.EdgeFactorization

/-!
# Binomial expansion of the Wilson-loop expectation (area law, AL4)

The strong-coupling expansion of `⟨W_C⟩·Z` starts from

    ∫ W · ∏_p (1 + f_p) dμ = ∑_{S ⊆ plaquettes} ∫ W · ∏_{p∈S} f_p dμ,

the integral-level binomial expansion over the plaquette set.  This file
proves that identity for bounded measurable `ℂ`-valued observables under
a probability measure (`integral_mul_prod_one_add`); the per-edge Haar
factorization of each term is `EdgeFactorization.lean`, and the
edge-balance vanishing of unspanned terms is
`sunHaarProb_fundMonomial_integral_zero` (AL3, banked).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory

/-- **Integral-level binomial expansion:** for bounded measurable
`W, f_p : α → ℂ` and a probability measure,
`∫ W·∏_p(1+f_p) = ∑_{S} ∫ W·∏_{p∈S} f_p` over all subsets `S`. -/
theorem integral_mul_prod_one_add {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {ι : Type*} (t : Finset ι) (W : α → ℂ) (f : ι → α → ℂ)
    (hWm : Measurable W) (CW : ℝ) (hWb : ∀ x, ‖W x‖ ≤ CW)
    (hfm : ∀ p, Measurable (f p)) (Cf : ℝ) (hfb : ∀ p x, ‖f p x‖ ≤ Cf) :
    ∫ x, W x * ∏ p ∈ t, (1 + f p x) ∂μ
      = ∑ S ∈ t.powerset, ∫ x, W x * ∏ p ∈ S, f p x ∂μ := by
  classical
  -- integrability of `W` (bounded measurable on a probability measure)
  have hIW : Integrable W μ := by
    have h1 : Integrable (fun _ : α => (1 : ℂ)) μ := integrable_const 1
    have h2 := h1.bdd_mul hWm.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ fun x => hWb x)
    simpa using h2
  -- integrability of each expansion term
  have hI : ∀ S ∈ t.powerset, Integrable
      (fun x => W x * ∏ p ∈ S, f p x) μ := by
    intro S _
    have hm : Measurable fun x => ∏ p ∈ S, f p x :=
      Finset.measurable_prod S fun p _ => hfm p
    have hb : ∀ x, ‖∏ p ∈ S, f p x‖ ≤ Cf ^ S.card := by
      intro x
      rw [norm_prod]
      calc ∏ p ∈ S, ‖f p x‖
          ≤ ∏ _p ∈ S, Cf :=
            Finset.prod_le_prod (fun p _ => norm_nonneg _)
              (fun p _ => hfb p x)
        _ = Cf ^ S.card := Finset.prod_const Cf
    have h2 := hIW.bdd_mul hm.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ hb)
    exact h2.congr (MeasureTheory.ae_of_all _ fun x => mul_comm _ _)
  -- pointwise binomial expansion, then swap `∫` and `∑`
  have hpt : (fun x => W x * ∏ p ∈ t, (1 + f p x))
      = fun x => ∑ S ∈ t.powerset, W x * ∏ p ∈ S, f p x := by
    funext x
    rw [Finset.prod_one_add, Finset.mul_sum]
  rw [hpt]
  exact MeasureTheory.integral_finset_sum t.powerset hI

end YangMills
