/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.SUNSelectionRule
import YangMills.L1_GibbsMeasure.PolymerExpansion
import YangMills.ClayCore.SchurL25

/-!
# The Wilson loop is a bona-fide observable

Non-vacuity closure for the interacting selection rule: the SU(n) Wilson
loop is **uniformly bounded** (`‖tr U‖ ≤ n` on special unitaries, from the
verified diagonal-entry bound) and **measurable**, hence **integrable**
against the Gibbs measure for any bounded measurable plaquette energy.
Thus the vanishing expectations proved in `GibbsSelectionRule.lean` concern
genuinely well-defined integrals — the selection rule has unambiguous
content.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory GaugeConfig

variable {d N : ℕ} [NeZero d] [NeZero N]

/-- Multiplication on `SU(n)` is jointly measurable (componentwise, through
the verified entry continuity — no product-Borel instance needed). -/
instance (n : ℕ) [NeZero n] :
    MeasurableMul₂ ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) := by
  refine ⟨Measurable.subtype_mk ?_⟩
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact ((ClayCore.continuous_val_entry i k).measurable.comp
    measurable_fst).mul
    ((ClayCore.continuous_val_entry k j).measurable.comp measurable_snd)

/-- Inversion on `SU(n)` is measurable (componentwise: the inverse of a
special unitary is its conjugate transpose). -/
instance (n : ℕ) [NeZero n] :
    MeasurableInv ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) := by
  refine ⟨Measurable.subtype_mk ?_⟩
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.star_apply]
  exact continuous_star.measurable.comp
    (ClayCore.continuous_val_entry j i).measurable

/-- **The Wilson loop is uniformly bounded:** `‖W_es(A)‖ ≤ n`, since every
diagonal entry of a special unitary matrix has norm at most one. -/
lemma norm_wilsonLoopSU_le {n : ℕ} [NeZero n]
    (A : GaugeConfig d N ↥(Matrix.specialUnitaryGroup (Fin n) ℂ))
    (es : List (ConcreteEdge d N)) :
    ‖wilsonLoopSU A es‖ ≤ n := by
  unfold wilsonLoopSU
  have hdiag : ∀ i : Fin n,
      ‖((wilsonLine A es :
        ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) :
          Matrix (Fin n) (Fin n) ℂ) i i‖ ≤ 1 := by
    intro i
    have h2 := ClayCore.normSq_val_diag_le_one (wilsonLine A es) i
    rw [ClayCore.complex_normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg (((wilsonLine A es :
      ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) i i)]
  calc ‖((wilsonLine A es :
        ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) :
          Matrix (Fin n) (Fin n) ℂ).trace‖
      ≤ ∑ i : Fin n, ‖((wilsonLine A es :
          ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) :
            Matrix (Fin n) (Fin n) ℂ) i i‖ := by
        rw [Matrix.trace]
        exact norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hdiag i
    _ = n := by simp

/-- **The Wilson line is measurable** in the configuration. -/
lemma measurable_wilsonLineSU {n : ℕ} [NeZero n]
    (es : List (ConcreteEdge d N)) :
    Measurable (fun A : GaugeConfig d N
      ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) => wilsonLine A es) := by
  unfold wilsonLine
  induction es with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    exact measurable_const
  | cons e t ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (measurable_config_apply e).mul ih

/-- **The Wilson loop is measurable** in the configuration. -/
lemma measurable_wilsonLoopSU {n : ℕ} [NeZero n]
    (es : List (ConcreteEdge d N)) :
    Measurable (fun A : GaugeConfig d N
      ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) => wilsonLoopSU A es) := by
  have hcont : Continuous (fun U : ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) =>
      ((U : Matrix (Fin n) (Fin n) ℂ)).trace) := by
    simp only [Matrix.trace, Matrix.diag]
    exact continuous_finset_sum _ fun i _ => ClayCore.continuous_val_entry i i
  exact hcont.measurable.comp (measurable_wilsonLineSU es)

/-- **The Wilson loop is integrable under the interacting Gibbs measure**
(bounded measurable plaquette energy) — so the selection-rule expectations
are genuinely well-defined integrals. -/
theorem integrable_wilsonLoopSU_gibbs {n : ℕ} [NeZero n]
    {pe : ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) → ℝ}
    (hpe_meas : Measurable pe) {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ) (es : List (ConcreteEdge d N)) :
    Integrable (fun A => wilsonLoopSU A es)
      (gibbsMeasure (d := d) (N := N) (sunHaarProb n) pe β) := by
  haveI := gibbsMeasure_isProbability' (d := d) (N := N)
    (sunHaarProb n) hpe_meas hpe β
  refine (MeasureTheory.integrable_const ((n : ℝ))).mono'
    (measurable_wilsonLoopSU es).aestronglyMeasurable ?_
  exact MeasureTheory.ae_of_all _ fun A => norm_wilsonLoopSU_le A es

end YangMills
