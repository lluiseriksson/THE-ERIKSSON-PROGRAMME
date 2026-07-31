/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/

import YangMills.OS.SU2WilsonReflectionSharp
import YangMills.ClayCore.SchurFundamentalOrthogonality

/-!
# A derived SU(2) commutator-word calculation

This module is deliberately outside the frozen `YangMills/OS/SU2WilsonReflection*`
lane.  It is based on the frozen source commit `a66b1c7d`, but is a new result
requiring its own audit.

The commutator convention is

`su2Commutator c₁ c₂ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹`.

The matrix moments are proved entry by entry from fundamental Schur
orthogonality.  No matrix-valued Bochner integral is introduced.
-/

noncomputable section

open Matrix Complex MeasureTheory
open scoped BigOperators

namespace YangMills.Derived

/-- The fixed commutator convention `[c₁,c₂] = c₁c₂c₁⁻¹c₂⁻¹`. -/
def su2Commutator (c₁ c₂ : SU2) : SU2 :=
  c₁ * c₂ * c₁⁻¹ * c₂⁻¹

@[simp]
theorem su2Commutator_self (c : SU2) : su2Commutator c c = 1 := by
  simp [su2Commutator]

theorem su2Commutator_inv (c₁ c₂ : SU2) :
    (su2Commutator c₁ c₂)⁻¹ = su2Commutator c₂ c₁ := by
  simp [su2Commutator, mul_assoc]

/-- Swapping the two independent variables sends the commutator to its inverse. -/
theorem su2Commutator_inv_swap (c₁ c₂ : SU2) :
    (su2Commutator c₁ c₂)⁻¹ = su2Commutator c₂ c₁ :=
  su2Commutator_inv c₁ c₂

/-- Entrywise first conjugation moment. -/
theorem su2_conjugation_entry_expand (c₁ c₂ : SU2) (i j : Fin 2) :
    (c₁ * c₂ * c₁⁻¹).val i j =
      ∑ l : Fin 2, ∑ k : Fin 2,
        c₁.val i k * c₂.val k l * star (c₁.val j l) := by
  change (c₁.val * c₂.val * (star c₁ : SU2).val) i j = _
  simp only [Matrix.mul_apply, Matrix.specialUnitaryGroup.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_mul]

set_option maxHeartbeats 200000 in
theorem su2_conjugation_entry_moment (c₂ : SU2) (i j : Fin 2) :
    (∫ c₁ : SU2, (c₁ * c₂ * c₁⁻¹).val i j ∂(sunHaarProb 2)) =
      (Matrix.trace c₂.val / 2) *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  classical
  simp_rw [su2_conjugation_entry_expand]
  rw [integral_finset_sum]
  · calc
      (∑ l : Fin 2, ∫ c₁ : SU2, ∑ k : Fin 2,
          c₁.val i k * c₂.val k l * star (c₁.val j l)
            ∂(sunHaarProb 2)) =
          ∑ l : Fin 2, ∑ k : Fin 2, c₂.val k l *
            (∫ c₁ : SU2, c₁.val i k * star (c₁.val j l)
              ∂(sunHaarProb 2)) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro k hk
          rw [show (fun c₁ : SU2 => c₁.val i k * c₂.val k l *
              star (c₁.val j l)) = fun c₁ => c₂.val k l *
                (c₁.val i k * star (c₁.val j l)) by funext c₁; ring]
          exact integral_const_mul (μ := sunHaarProb 2) _ _
        · intro k hk
          have hc : Continuous (fun c₁ : SU2 =>
              c₁.val i k * c₂.val k l * star (c₁.val j l)) :=
            ((YangMills.ClayCore.continuous_val_entry i k).mul
              continuous_const).mul
                ((YangMills.ClayCore.continuous_val_entry j l).star)
          exact hc.integrable_of_hasCompactSupport (μ := sunHaarProb 2)
            (HasCompactSupport.of_compactSpace _)
      _ = ∑ l : Fin 2, ∑ k : Fin 2, c₂.val k l *
          (if i = j ∧ k = l then (1 : ℂ) / 2 else 0) := by
        simp_rw [YangMills.ClayCore.sunHaarProb_fundamental_entry_orthogonality]
        norm_num
      _ = (Matrix.trace c₂.val / 2) *
          (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
        fin_cases i <;> fin_cases j <;>
          simp [Fin.sum_univ_two, Matrix.trace, Matrix.diag]
          <;> ring
  · intro l hl
    exact integrable_finset_sum Finset.univ fun k hk => by
      have hc : Continuous (fun c₁ : SU2 =>
          c₁.val i k * c₂.val k l * star (c₁.val j l)) :=
        ((YangMills.ClayCore.continuous_val_entry i k).mul
          continuous_const).mul
            ((YangMills.ClayCore.continuous_val_entry j l).star)
      exact hc.integrable_of_hasCompactSupport (μ := sunHaarProb 2)
        (HasCompactSupport.of_compactSpace _)

/-- Entrywise second moment `∫ χ(c)c⁻¹ = (1/2)I`. -/
theorem su2_inv_val_entry (c : SU2) (i j : Fin 2) :
    c⁻¹.val i j = star (c.val j i) := by
  change (star c : SU2).val i j = _
  simp only [Matrix.specialUnitaryGroup.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

set_option maxHeartbeats 200000 in
theorem su2_trace_inv_entry_moment (i j : Fin 2) :
    (∫ c : SU2, Matrix.trace c.val * c⁻¹.val i j ∂(sunHaarProb 2)) =
      ((1 : ℂ) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  classical
  simp_rw [su2_inv_val_entry, Matrix.trace, Matrix.diag]
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum]
  · simp_rw [YangMills.ClayCore.sunHaarProb_fundamental_entry_orthogonality]
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_two]
  · intro a ha
    exact ((YangMills.ClayCore.continuous_val_entry a a).mul
      ((YangMills.ClayCore.continuous_val_entry j i).star)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- The exact commutator moment, stated entrywise to avoid matrix-valued integration. -/
theorem su2_commutator_entry_moment (i j : Fin 2) :
    (∫ c₂ : SU2, ∫ c₁ : SU2,
      (su2Commutator c₁ c₂).val i j ∂(sunHaarProb 2) ∂(sunHaarProb 2)) =
      ((1 : ℂ) / 4) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  classical
  have hinner (c₂ : SU2) :
      (∫ c₁ : SU2, (su2Commutator c₁ c₂).val i j ∂(sunHaarProb 2)) =
        (Matrix.trace c₂.val / 2) * c₂⁻¹.val i j := by
    unfold su2Commutator
    change (∫ c₁ : SU2, ∑ a : Fin 2,
      (c₁ * c₂ * c₁⁻¹).val i a * c₂⁻¹.val a j
        ∂(sunHaarProb 2)) = _
    rw [integral_finset_sum]
    · calc
        (∑ a : Fin 2, ∫ c₁ : SU2,
            (c₁ * c₂ * c₁⁻¹).val i a * c₂⁻¹.val a j
              ∂(sunHaarProb 2)) =
            ∑ a : Fin 2, (Matrix.trace c₂.val / 2) *
              (1 : Matrix (Fin 2) (Fin 2) ℂ) i a * c₂⁻¹.val a j := by
          apply Finset.sum_congr rfl
          intro a ha
          calc
            (∫ c₁ : SU2,
                (c₁ * c₂ * c₁⁻¹).val i a * c₂⁻¹.val a j
                  ∂(sunHaarProb 2)) =
                (∫ c₁ : SU2, (c₁ * c₂ * c₁⁻¹).val i a
                  ∂(sunHaarProb 2)) * c₂⁻¹.val a j := by
              exact integral_mul_const (μ := sunHaarProb 2) _ _
            _ = (Matrix.trace c₂.val / 2) *
                (1 : Matrix (Fin 2) (Fin 2) ℂ) i a * c₂⁻¹.val a j := by
              rw [su2_conjugation_entry_moment c₂ i a]
        _ = (Matrix.trace c₂.val / 2) * c₂⁻¹.val i j := by
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.one_apply]
    · intro a ha
      have hc : Continuous (fun c₁ : SU2 =>
          (c₁ * c₂ * c₁⁻¹).val i a * c₂⁻¹.val a j) :=
        ((YangMills.ClayCore.continuous_val_entry i a).comp
          ((continuous_id.mul continuous_const).mul continuous_inv)).mul
            continuous_const
      exact hc.integrable_of_hasCompactSupport (μ := sunHaarProb 2)
        (HasCompactSupport.of_compactSpace _)
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  calc
    (∫ c₂ : SU2, (Matrix.trace c₂.val / 2) * c₂⁻¹.val i j
        ∂(sunHaarProb 2)) =
        ∫ c₂ : SU2, (1 / 2 : ℂ) *
          (Matrix.trace c₂.val * c₂⁻¹.val i j)
            ∂(sunHaarProb 2) := by
          apply integral_congr_ae
          filter_upwards [] with c₂
          ring
    _ = (1 / 2 : ℂ) *
        (∫ c₂ : SU2, Matrix.trace c₂.val * c₂⁻¹.val i j
          ∂(sunHaarProb 2)) := by
      exact integral_const_mul _ _
    _ = (1 / 4 : ℂ) *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
      rw [su2_trace_inv_entry_moment]
      ring

/-- The inverse commutator has the same entrywise mean, by swapping variables. -/
theorem su2_commutator_inv_entry_moment (i j : Fin 2) :
    (∫ c₁ : SU2, ∫ c₂ : SU2,
      ((su2Commutator c₁ c₂)⁻¹).val i j
        ∂(sunHaarProb 2) ∂(sunHaarProb 2)) =
      ((1 : ℂ) / 4) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  simp_rw [su2Commutator_inv]
  exact su2_commutator_entry_moment i j

/-- Conjugating the scalar entry moment commutes with both Haar integrals. -/
theorem su2_commutator_inv_star_entry_moment (i j : Fin 2) :
    (∫ c₁ : SU2, ∫ c₂ : SU2,
      star ((su2Commutator c₁ c₂)⁻¹.val i j)
        ∂(sunHaarProb 2) ∂(sunHaarProb 2)) =
      ((1 : ℂ) / 4) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  calc
    (∫ c₁ : SU2, ∫ c₂ : SU2,
        star ((su2Commutator c₁ c₂)⁻¹.val i j)
          ∂(sunHaarProb 2) ∂(sunHaarProb 2)) =
        ∫ c₁ : SU2, star (∫ c₂ : SU2,
          (su2Commutator c₁ c₂)⁻¹.val i j ∂(sunHaarProb 2))
            ∂(sunHaarProb 2) := by
      apply integral_congr_ae
      filter_upwards [] with c₁
      exact integral_conj
    _ = star (∫ c₁ : SU2, ∫ c₂ : SU2,
        (su2Commutator c₁ c₂)⁻¹.val i j
          ∂(sunHaarProb 2) ∂(sunHaarProb 2)) := integral_conj
    _ = ((1 : ℂ) / 4) *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
      rw [su2_commutator_inv_entry_moment]
      fin_cases i <;> fin_cases j <;> norm_num

/-- Scalar expansion used after the conditioned right translation. -/
theorem su2_trace_mul_star_expand (u k : SU2) :
    star (YangMills.OS.su2TraceObservable (u * k)) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        star (u.val i j) * star (k.val j i) := by
  change star (∑ i : Fin 2, ∑ j : Fin 2,
    u.val i j * k.val j i) = _
  change (starRingEnd ℂ) (∑ i : Fin 2, ∑ j : Fin 2,
    u.val i j * k.val j i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  rfl

/-- Generic Fubini gate used by the intended four-Haar assembly.  The
integrability hypothesis is explicit and does not mention SU(2). -/
theorem integral_integral_swap_of_integrable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y → ℂ)
    [SFinite μ] [SFinite ν]
    (hf : Integrable (Function.uncurry f) (μ.prod ν)) :
    (∫ x, ∫ y, f x y ∂ν ∂μ) = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  integral_integral_swap hf

/-- The concrete four-Haar commutator-word quadratic form.  This definition
does not contain a factor `1/4`. -/
def su2CommutatorQuadraticForm (β : ℝ) : ℂ :=
  ∫ c₁ : SU2, ∫ c₂ : SU2, ∫ x : SU2, ∫ y : SU2,
    star (YangMills.OS.su2TraceObservable x) *
      YangMills.OS.su2WilsonCrossingKernel β
        (x * su2Commutator c₁ c₂) y *
      YangMills.OS.su2TraceObservable y
    ∂(sunHaarProb 2) ∂(sunHaarProb 2)
    ∂(sunHaarProb 2) ∂(sunHaarProb 2)

/-- The unchanged base quadratic form from the frozen producer. -/
def su2BaseQuadraticForm (β : ℝ) : ℂ :=
  YangMills.OS.kernelIntegralForm (sunHaarProb 2)
    (YangMills.OS.su2WilsonCrossingKernel β)
    YangMills.OS.su2TraceObservable

/-- Fibrewise right translation in `x`, with `c₁,c₂` fixed.  The commutator
is not treated as Haar: it is merely the fixed translating element. -/
theorem su2_conditioned_right_translation
    (β : ℝ) (c₁ c₂ : SU2) :
    (∫ x : SU2, ∫ y : SU2,
      star (YangMills.OS.su2TraceObservable x) *
        YangMills.OS.su2WilsonCrossingKernel β
          (x * su2Commutator c₁ c₂) y *
        YangMills.OS.su2TraceObservable y
      ∂(sunHaarProb 2) ∂(sunHaarProb 2)) =
    ∫ u : SU2, ∫ y : SU2,
      star (YangMills.OS.su2TraceObservable
        (u * (su2Commutator c₁ c₂)⁻¹)) *
        YangMills.OS.su2WilsonCrossingKernel β u y *
        YangMills.OS.su2TraceObservable y
      ∂(sunHaarProb 2) ∂(sunHaarProb 2) := by
  let k : SU2 := su2Commutator c₁ c₂
  let f : SU2 → ℂ := fun x => ∫ y : SU2,
    star (YangMills.OS.su2TraceObservable x) *
      YangMills.OS.su2WilsonCrossingKernel β (x * k) y *
      YangMills.OS.su2TraceObservable y ∂(sunHaarProb 2)
  have h := MeasureTheory.integral_mul_right_eq_self
    (μ := sunHaarProb 2) f k⁻¹
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with u
  simp [f, k, mul_assoc]

/-- The certified lower bound for the quarter-scaled frozen quadratic form.
It is the downstream inequality used once the remaining Fubini assembly has
identified the concrete commutator form with this expression. -/
theorem quarter_su2BaseQuadraticForm_lower
    (β : ℝ) (hβ : 0 ≤ β) :
    β / 16 ≤ (((1 : ℂ) / 4) * su2BaseQuadraticForm β).re := by
  have h := YangMills.OS.su2Trace_crossing_lower β hβ
  change β / 16 ≤ (((1 : ℂ) / 4) *
    YangMills.OS.kernelIntegralForm (sunHaarProb 2)
      (YangMills.OS.su2WilsonCrossingKernel β)
      YangMills.OS.su2TraceObservable).re
  have hs : (1 : ℂ) / 4 = (((1 : ℝ) / 4 : ℝ) : ℂ) := by norm_num
  rw [hs]
  rw [mul_re]
  simp
  linarith

theorem quarter_su2BaseQuadraticForm_strict
    (β : ℝ) (hβ : 0 < β) :
    0 < (((1 : ℂ) / 4) * su2BaseQuadraticForm β).re := by
  exact (div_pos hβ (by norm_num : (0 : ℝ) < 16)).trans_le
    (quarter_su2BaseQuadraticForm_lower β hβ.le)

/-- Non-vacuity witness: the observable is nonzero at the identity. -/
theorem su2TraceObservable_one_nonzero :
    YangMills.OS.su2TraceObservable (1 : SU2) ≠ 0 := by
  norm_num [YangMills.OS.su2TraceObservable, Matrix.trace,
    Matrix.diag_apply, Fin.sum_univ_two]

/-- The Haar probability measure used by the construction is not zero. -/
theorem sunHaarProb_two_ne_zero : (sunHaarProb 2) ≠ 0 := by
  intro hzero
  have hmass : (sunHaarProb 2) Set.univ = 1 := measure_univ
  rw [hzero] at hmass
  simp at hmass

/-- Non-vacuity witness at the concrete positive coupling `β=1`. -/
theorem quarter_su2BaseQuadraticForm_one_strict :
    0 < (((1 : ℂ) / 4) * su2BaseQuadraticForm 1).re := by
  exact quarter_su2BaseQuadraticForm_strict 1 (by norm_num)

end YangMills.Derived

end
