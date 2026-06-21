/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFKsharp
import YangMills.RG.AppendixFLocalSummability

/-!
# Appendix F: source-shaped first `K#` estimate

This module combines the already-verified finite pieces for the first
Appendix-F activity:

* raw Mayer product norm control;
* target-fiber entropy;
* with-holes modified-metric stitching;
* local contained-support summability; and
* the generic probability-integral transfer for `K#`.

The rate here is the first-gas rate `kappa - kappa0 - 2`.  The final residual
`H#` rate `kappa - 3*kappa0 - 3` belongs to the later second-gas/Ursell step
and is not used in this file.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open MeasureTheory
open Finset
open scoped BigOperators

private theorem appendixF_exp_mul_sub_one_le_mul_exp_two_mul
    {a m : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hm0 : 0 ≤ m) :
    Real.exp (a * m) - 1 ≤ a * Real.exp (2 * m) := by
  have hb0 : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hsum : a + (1 - a) = (1 : ℝ) := by ring
  have hconvFn := (convexOn_exp : ConvexOn ℝ Set.univ Real.exp).2
  have hconv := hconvFn (x := m) (by simp) (y := 0) (by simp)
    (a := a) (b := 1 - a) ha0 hb0 hsum
  have hconv' : Real.exp (a * m) ≤ a * Real.exp m + (1 - a) := by
    simpa [smul_eq_mul] using hconv
  have hsub : Real.exp (a * m) - 1 ≤ a * (Real.exp m - 1) := by
    nlinarith
  have hminus : Real.exp m - 1 ≤ Real.exp m := by linarith
  have hstep : a * (Real.exp m - 1) ≤ a * Real.exp m :=
    mul_le_mul_of_nonneg_left hminus ha0
  have hexpmono : Real.exp m ≤ Real.exp (2 * m) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hstep2 : a * Real.exp m ≤ a * Real.exp (2 * m) :=
    mul_le_mul_of_nonneg_left hexpmono ha0
  exact hsub.trans (hstep.trans hstep2)

private theorem appendixFHole_metricCoverWeight_le_targetEntropyProduct
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    {C : Finset (OmegaPolymerType HF z)}
    {H₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hκ : κ₀ ≤ κ)
    (hC : C ∈ appendixFTargetFiber
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y) :
    appendixFMetricCoverWeight
        (fun X : OmegaPolymerType HF z =>
          discreteModifiedMetric HF X.val + 1)
        H₀ κ C
      ≤
    appendixFHoleExpWeight HF (κ - κ₀) Y *
      ∏ X ∈ C, (2 * H₀) * appendixFHoleExpWeight HF κ₀ X.val := by
  classical
  let metric : OmegaPolymerType HF z → ℕ := fun X =>
    discreteModifiedMetric HF X.val + 1
  let S : ℝ := ∑ X ∈ C, (metric X : ℝ)
  let mY : ℝ := ((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)
  have hmetricNat :
      discreteModifiedMetric HF Y + 1
        ≤ ∑ X ∈ C, (discreteModifiedMetric HF X.val + 1) :=
    appendixFHoleTargetFiber_discreteModifiedMetric_add_one_le_sum
      HF z Λ hC
  have hmetric : mY ≤ S := by
    dsimp [mY, S, metric]
    exact_mod_cast hmetricNat
  have hrate_nonneg : 0 ≤ κ - κ₀ := sub_nonneg.mpr hκ
  have hexp_rate :
      Real.exp (-(κ * S)) ≤
        Real.exp (-((κ - κ₀) * mY)) * Real.exp (-(κ₀ * S)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hmul : (κ - κ₀) * mY ≤ (κ - κ₀) * S :=
      mul_le_mul_of_nonneg_left hmetric hrate_nonneg
    nlinarith
  have hbase_nonneg : 0 ≤ (2 * H₀) ^ C.card :=
    pow_nonneg (mul_nonneg zero_le_two hH₀) C.card
  calc
    appendixFMetricCoverWeight metric H₀ κ C
        = (2 * H₀) ^ C.card * Real.exp (-(κ * S)) := by
          simp [appendixFMetricCoverWeight, metric, S]
    _ ≤
      (2 * H₀) ^ C.card *
        (Real.exp (-((κ - κ₀) * mY)) * Real.exp (-(κ₀ * S))) := by
          exact mul_le_mul_of_nonneg_left hexp_rate hbase_nonneg
    _ =
      Real.exp (-((κ - κ₀) * mY)) *
        ((2 * H₀) ^ C.card * Real.exp (-(κ₀ * S))) := by
          ring
    _ =
      appendixFHoleExpWeight HF (κ - κ₀) Y *
        ∏ X ∈ C, (2 * H₀) * appendixFHoleExpWeight HF κ₀ X.val := by
          have hprod :
              (∏ X ∈ C,
                  (2 * H₀) * appendixFHoleExpWeight HF κ₀ X.val)
                =
              (2 * H₀) ^ C.card * Real.exp (-(κ₀ * S)) := by
            calc
              (∏ X ∈ C,
                  (2 * H₀) * appendixFHoleExpWeight HF κ₀ X.val)
                  =
                (∏ _X ∈ C, (2 * H₀)) *
                  ∏ X ∈ C, appendixFHoleExpWeight HF κ₀ X.val := by
                    rw [Finset.prod_mul_distrib]
              _ =
                (2 * H₀) ^ C.card *
                  ∏ X ∈ C, appendixFHoleExpWeight HF κ₀ X.val := by
                    rw [Finset.prod_const]
              _ =
                (2 * H₀) ^ C.card *
                  Real.exp (∑ X ∈ C,
                    -(κ₀ * ((metric X : ℕ) : ℝ))) := by
                    rw [Real.exp_sum]
                    simp [appendixFHoleExpWeight, metric]
              _ =
                (2 * H₀) ^ C.card * Real.exp (-(κ₀ * S)) := by
                    have hsum :
                        (∑ X ∈ C,
                            -(κ₀ * ((metric X : ℕ) : ℝ)))
                          = -(κ₀ * S) := by
                      calc
                        (∑ X ∈ C,
                            -(κ₀ * ((metric X : ℕ) : ℝ)))
                            =
                        -(∑ X ∈ C,
                          κ₀ * ((metric X : ℕ) : ℝ)) := by
                            rw [Finset.sum_neg_distrib]
                      _ =
                        -(κ₀ * ∑ X ∈ C, ((metric X : ℕ) : ℝ)) := by
                            rw [← Finset.mul_sum]
                        _ = -(κ₀ * S) := by rfl
                    rw [hsum]
          rw [hprod]
          simp [appendixFHoleExpWeight, mY]

/-- Exact pointwise first-activity estimate before linearizing the
`exp(...) - 1` term.  This is the finite meeting point of the raw metric
bound, target-fiber entropy, metric stitching, and contained-support local
summability. -/
theorem norm_appendixFHoleConnectedLocalActivity_globalEval_le_expSubOne
    {d L : ℕ} [NeZero L]
    {β : Type*} {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x) (φ : ∀ _ : Cube d L, β)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hH₀_one : H₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hraw : ∀ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hlocal :
      (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y),
        appendixFHoleExpWeight HF κ₀ X.val)
        ≤
      (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) * K₀) :
    ‖(appendixFHoleConnectedLocalActivity
        HF z Λ H Y).globalEval ψ φ‖
      ≤
    appendixFHoleExpWeight HF (κ - κ₀) Y *
      (Real.exp
        (2 * H₀ * K₀ *
          (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ))) - 1) := by
  classical
  let metric : OmegaPolymerType HF z → ℕ := fun X =>
    discreteModifiedMetric HF X.val + 1
  let fiber := appendixFTargetFiber
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ Y
  let w : OmegaPolymerType HF z → ℝ := fun X =>
    (2 * H₀) * appendixFHoleExpWeight HF κ₀ X.val
  have hraw_metric : ∀ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * Real.exp (-κ * (metric X : ℝ)) := by
    intro X hX
    simpa [appendixFHoleExpWeight, metric] using hraw X hX
  have hactivity :
      ‖appendixFHoleConnectedMayerActivity HF z Λ
          (fun X => Complex.exp ((H X).globalEval ψ φ) - 1) Y‖ ≤
        ∑ C ∈ fiber, appendixFMetricCoverWeight metric H₀ κ C := by
    simpa [fiber, appendixFMetricCoverWeight, metric] using
      norm_appendixFHoleConnectedMayerActivity_expSubOne_le_metricCoverSum
        HF z Λ metric
        (fun X : OmegaPolymerType HF z => (H X).globalEval ψ φ)
        Y H₀ κ hH₀ hH₀_one (hκ₀.trans hκ) hraw_metric
  have hterm :
      (∑ C ∈ fiber, appendixFMetricCoverWeight metric H₀ κ C)
        ≤
      appendixFHoleExpWeight HF (κ - κ₀) Y *
        ∑ C ∈ fiber, ∏ X ∈ C, w X := by
    have hfactor_nonneg :
        0 ≤ appendixFHoleExpWeight HF (κ - κ₀) Y :=
      appendixFHoleExpWeight_nonneg HF (κ - κ₀) Y
    calc
      (∑ C ∈ fiber, appendixFMetricCoverWeight metric H₀ κ C)
          ≤
        ∑ C ∈ fiber,
          appendixFHoleExpWeight HF (κ - κ₀) Y *
            ∏ X ∈ C, w X := by
            refine Finset.sum_le_sum ?_
            intro C hC
            simpa [w, metric, fiber] using
              appendixFHole_metricCoverWeight_le_targetEntropyProduct
                HF z Λ hH₀ hκ hC
      _ =
        appendixFHoleExpWeight HF (κ - κ₀) Y *
          ∑ C ∈ fiber, ∏ X ∈ C, w X := by
            rw [Finset.mul_sum]
  have hw_nonneg : ∀ X, X ∈ Λ → 0 ≤ w X := by
    intro X hX
    exact mul_nonneg (mul_nonneg zero_le_two hH₀)
      (appendixFHoleExpWeight_nonneg HF κ₀ X.val)
  have hfiber_entropy :
      (∑ C ∈ fiber, ∏ X ∈ C, w X)
        ≤
      Real.exp
          (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y), w X) - 1 := by
    simpa [fiber, w] using
      appendixFTargetFiber_prod_le_exp_sub_one
        (Finset.univ : Finset (Cube d L))
        (fun X : OmegaPolymerType HF z => skeleton HF X.val)
        (fun X : OmegaPolymerType HF z => X.val)
        Λ Y w hw_nonneg
  have hw_sum :
      (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y), w X)
        ≤
      2 * H₀ * K₀ *
        (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) := by
    calc
      (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y), w X)
          =
        (2 * H₀) *
          (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y),
            appendixFHoleExpWeight HF κ₀ X.val) := by
            simp [w, Finset.mul_sum]
      _ ≤
        (2 * H₀) *
          ((((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) * K₀) := by
            exact mul_le_mul_of_nonneg_left hlocal
              (mul_nonneg zero_le_two hH₀)
      _ =
        2 * H₀ * K₀ *
          (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) := by
            ring
  have hexp_entropy :
      Real.exp
          (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y), w X) - 1
        ≤
      Real.exp
        (2 * H₀ * K₀ *
          (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ))) - 1 := by
    have h := Real.exp_le_exp.mpr hw_sum
    linarith
  have hentropy_target :
      appendixFHoleExpWeight HF (κ - κ₀) Y *
        (∑ C ∈ fiber, ∏ X ∈ C, w X)
        ≤
      appendixFHoleExpWeight HF (κ - κ₀) Y *
        (Real.exp
          (2 * H₀ * K₀ *
            (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ))) - 1) := by
    exact mul_le_mul_of_nonneg_left
      (hfiber_entropy.trans hexp_entropy)
      (appendixFHoleExpWeight_nonneg HF (κ - κ₀) Y)
  calc
    ‖(appendixFHoleConnectedLocalActivity HF z Λ H Y).globalEval ψ φ‖
        =
      ‖appendixFHoleConnectedMayerActivity HF z Λ
          (fun X => Complex.exp ((H X).globalEval ψ φ) - 1) Y‖ := by
          rw [appendixFHoleConnectedLocalActivity_globalEval]
    _ ≤ ∑ C ∈ fiber, appendixFMetricCoverWeight metric H₀ κ C :=
      hactivity
    _ ≤ appendixFHoleExpWeight HF (κ - κ₀) Y *
        ∑ C ∈ fiber, ∏ X ∈ C, w X := hterm
    _ ≤ appendixFHoleExpWeight HF (κ - κ₀) Y *
        (Real.exp
          (2 * H₀ * K₀ *
            (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ))) - 1) :=
      hentropy_target

/-- Raw pointwise metric decay plus strong measurability makes the connected
first activity integrable.

This is the explicit compiler for the `hint` obligation used by the integrated
`K#` estimates: the analytic/source side may provide measurability of the
connected integrand, while the already-verified finite Appendix-F estimate
supplies a uniform pointwise bound from the raw one-polymer decay. -/
theorem integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay
    {d L : ℕ} [NeZero L]
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hH₀_one : H₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hlocal :
      (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y),
        appendixFHoleExpWeight HF κ₀ X.val)
        ≤
      (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) * K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hmeas :
      AEStronglyMeasurable
        (fun φ : (∀ _ : Cube d L, β) =>
          (appendixFHoleConnectedLocalActivity
            HF z Λ H Y).globalEval ψ φ)
        (Measure.pi fun _ : Cube d L => μ)) :
    Integrable
      (fun φ : (∀ _ : Cube d L, β) =>
        (appendixFHoleConnectedLocalActivity
          HF z Λ H Y).globalEval ψ φ)
      (Measure.pi fun _ : Cube d L => μ) := by
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Cube d L => μ) :=
    inferInstance
  refine Integrable.of_bound hmeas
    (appendixFHoleExpWeight HF (κ - κ₀) Y *
      (Real.exp
        (2 * H₀ * K₀ *
          (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ))) - 1)) ?_
  exact Filter.Eventually.of_forall fun φ =>
    norm_appendixFHoleConnectedLocalActivity_globalEval_le_expSubOne
      HF z Λ H Y ψ φ hH₀ hH₀_one hκ₀ hκ (hraw φ) hlocal

/-- Ordinary strong measurability form of
`integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay`.

This adapter keeps source-facing measurability proofs in the common
`StronglyMeasurable` form and derives the a.e. strong measurability needed by
the generic probability-integrability compiler. -/
theorem integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay_of_stronglyMeasurable
    {d L : ℕ} [NeZero L]
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    (Y : Finset (Cube d L))
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hH₀_one : H₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hlocal :
      (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y),
        appendixFHoleExpWeight HF κ₀ X.val)
        ≤
      (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) * K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hmeas :
      StronglyMeasurable
        (fun φ : (∀ _ : Cube d L, β) =>
          (appendixFHoleConnectedLocalActivity
            HF z Λ H Y).globalEval ψ φ)) :
    Integrable
      (fun φ : (∀ _ : Cube d L, β) =>
        (appendixFHoleConnectedLocalActivity
          HF z Λ H Y).globalEval ψ φ)
      (Measure.pi fun _ : Cube d L => μ) :=
  integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay
    HF z Λ H μ Y ψ hH₀ hH₀_one hκ₀ hκ hlocal hraw
    hmeas.aestronglyMeasurable

/-- Source-shaped integrated exact `K#` estimate from raw pointwise metric
decay and local contained-support summability.  Integrability stays explicit,
and the exponential-minus-one factor is intentionally not linearized here. -/
theorem norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay
    {d L : ℕ} [NeZero L]
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    {Y : Finset (Cube d L)}
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hH₀_one : H₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hlocal :
      (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y),
        appendixFHoleExpWeight HF κ₀ X.val)
        ≤
      (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) * K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hint : Integrable
      (fun φ =>
        (appendixFHoleConnectedLocalActivity
          HF z Λ H Y).globalEval ψ φ)
      (Measure.pi fun _ : Cube d L => μ)) :
    ‖(appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ‖
      ≤
    appendixFHoleExpWeight HF (κ - κ₀) Y *
      (Real.exp
        (2 * H₀ * K₀ *
          (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ))) - 1) := by
  classical
  exact norm_appendixFHoleKsharp_globalEval_le
    HF z Λ H μ Y ψ hint
    (fun φ =>
      norm_appendixFHoleConnectedLocalActivity_globalEval_le_expSubOne
        HF z Λ H Y ψ φ hH₀ hH₀_one hκ₀ hκ
        (hraw φ) hlocal)

/-- Rooted-summability version of the integrated exact `K#` estimate.  This is
the form that consumes the local adapter from `AppendixFLocalSummability`. -/
theorem norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted
    {d L : ℕ} [NeZero L]
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hκ₀ : 0 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hint : Integrable
      (fun φ =>
        (appendixFHoleConnectedLocalActivity
          HF z Λ H Y).globalEval ψ φ)
      (Measure.pi fun _ : Cube d L => μ)) :
    ‖(appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ‖
      ≤
    appendixFHoleExpWeight HF (κ - κ₀) Y *
      (Real.exp
        (2 * H₀ * K₀ *
          (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ))) - 1) := by
  classical
  have hlocal :
      (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y),
        appendixFHoleExpWeight HF κ₀ X.val)
        ≤
      (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) * K₀ :=
    appendixFHole_containedWeightSum_le_metric_mul_of_rooted
      HF z Λ (fun X => appendixFHoleExpWeight HF κ₀ X.val)
      (fun X _hX => appendixFHoleExpWeight_nonneg HF κ₀ X.val)
      hK₀ hroot hY
  exact norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay
    HF z Λ H μ ψ hH₀ hH₀_one hκ₀ hκ
    hlocal hraw hint

/-- Rooted-summability version of the raw integrability compiler. -/
theorem integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay_rooted
    {d L : ℕ} [NeZero L]
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hκ₀ : 0 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hmeas :
      AEStronglyMeasurable
        (fun φ : (∀ _ : Cube d L, β) =>
          (appendixFHoleConnectedLocalActivity
            HF z Λ H Y).globalEval ψ φ)
        (Measure.pi fun _ : Cube d L => μ)) :
    Integrable
      (fun φ : (∀ _ : Cube d L, β) =>
        (appendixFHoleConnectedLocalActivity
          HF z Λ H Y).globalEval ψ φ)
      (Measure.pi fun _ : Cube d L => μ) := by
  have hlocal :
      (∑ X ∈ Λ.filter (fun X => X.val ⊆ Y),
        appendixFHoleExpWeight HF κ₀ X.val)
        ≤
      (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ)) * K₀ :=
    appendixFHole_containedWeightSum_le_metric_mul_of_rooted
      HF z Λ (fun X => appendixFHoleExpWeight HF κ₀ X.val)
      (fun X _hX => appendixFHoleExpWeight_nonneg HF κ₀ X.val)
      hK₀ hroot hY
  exact
    integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay
      HF z Λ H μ Y ψ hH₀ hH₀_one hκ₀ hκ hlocal hraw hmeas

/-- Ordinary strong measurability form of the rooted raw integrability compiler. -/
theorem integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay_rooted_of_stronglyMeasurable
    {d L : ℕ} [NeZero L]
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hκ₀ : 0 ≤ κ₀) (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hmeas :
      StronglyMeasurable
        (fun φ : (∀ _ : Cube d L, β) =>
          (appendixFHoleConnectedLocalActivity
            HF z Λ H Y).globalEval ψ φ)) :
    Integrable
      (fun φ : (∀ _ : Cube d L, β) =>
        (appendixFHoleConnectedLocalActivity
          HF z Λ H Y).globalEval ψ φ)
      (Measure.pi fun _ : Cube d L => μ) :=
  integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay_rooted
    HF z Λ H μ hY ψ hH₀ hH₀_one hK₀ hκ₀ hκ hroot hraw
    hmeas.aestronglyMeasurable

/-- Linearized rooted first-activity estimate at the Appendix-F `K#` rate.

The exact estimate above has the nonlinear factor
`exp (2 * H₀ * K₀ * (d_M(Y)+1)) - 1`.  Under the standard smallness
`2 * H₀ * K₀ ≤ 1`, convexity of `exp` extracts the scalar
`2 * H₀ * K₀` and pays the two spare metric units, producing the canonical
first-gas rate `κ - κ₀ - 2`. -/
theorem norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted
    {d L : ℕ} [NeZero L]
    {β : Type*} [MeasurableSpace β]
    {Ψ : Cube d L → Type*}
    (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    (H : OmegaPolymerType HF z →
      LocalActivity (Cube d L) Ψ (fun _ => β) ℂ)
    (μ : Measure β) [IsProbabilityMeasure μ]
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val)
      Λ)
    (ψ : ∀ x, Ψ x)
    {H₀ K₀ κ κ₀ : ℝ}
    (hH₀ : 0 ≤ H₀)
    (hH₀_one : H₀ ≤ 1)
    (hK₀ : 0 ≤ K₀)
    (hsmall : 2 * H₀ * K₀ ≤ 1)
    (hκ₀ : 0 ≤ κ₀)
    (hκ : κ₀ ≤ κ)
    (hroot : ∀ r : Cube d L,
      (∑ X ∈ Λ.filter
          (fun X => r ∈ skeleton HF X.val),
        appendixFHoleExpWeight HF κ₀ X.val) ≤ K₀)
    (hraw : ∀ φ X, X ∈ Λ →
      ‖(H X).globalEval ψ φ‖ ≤
        H₀ * appendixFHoleExpWeight HF κ X.val)
    (hint : Integrable
      (fun φ =>
        (appendixFHoleConnectedLocalActivity
          HF z Λ H Y).globalEval ψ φ)
      (Measure.pi fun _ : Cube d L => μ)) :
    ‖(appendixFHoleKsharp HF z Λ H μ Y).globalEval ψ‖ ≤
      (2 * H₀ * K₀) *
        appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y := by
  classical
  let a : ℝ := 2 * H₀ * K₀
  let m : ℝ := (((discreteModifiedMetric HF Y + 1 : ℕ) : ℝ))
  have hbase :=
    norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted
      HF z Λ H μ hY ψ hH₀ hH₀_one hK₀ hκ₀ hκ hroot hraw hint
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (mul_nonneg zero_le_two hH₀) hK₀
  have hm0 : 0 ≤ m := by
    dsimp [m]
    positivity
  have hlin : Real.exp (a * m) - 1 ≤ a * Real.exp (2 * m) :=
    appendixF_exp_mul_sub_one_le_mul_exp_two_mul ha0
      (by simpa [a] using hsmall) hm0
  have hmul :
      appendixFHoleExpWeight HF (κ - κ₀) Y *
          (Real.exp (a * m) - 1) ≤
        appendixFHoleExpWeight HF (κ - κ₀) Y *
          (a * Real.exp (2 * m)) :=
    mul_le_mul_of_nonneg_left hlin
      (appendixFHoleExpWeight_nonneg HF (κ - κ₀) Y)
  have hrewrite :
      appendixFHoleExpWeight HF (κ - κ₀) Y *
          (a * Real.exp (2 * m)) =
        a * appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y := by
    have hrate : -((κ - κ₀) * m) + 2 * m =
        -(appendixFKsharpRate κ κ₀ * m) := by
      unfold appendixFKsharpRate
      ring
    calc
      appendixFHoleExpWeight HF (κ - κ₀) Y *
          (a * Real.exp (2 * m))
          = a * (Real.exp (-((κ - κ₀) * m)) * Real.exp (2 * m)) := by
            simp [appendixFHoleExpWeight, m]
            ring
      _ = a * Real.exp (-((κ - κ₀) * m) + 2 * m) := by
            rw [Real.exp_add]
      _ = a * Real.exp (-(appendixFKsharpRate κ κ₀ * m)) := by
            rw [hrate]
      _ = a * appendixFHoleExpWeight HF (appendixFKsharpRate κ κ₀) Y := by
            simp [appendixFHoleExpWeight, m]
  exact hbase.trans (hmul.trans (le_of_eq hrewrite))

end YangMills.RG
