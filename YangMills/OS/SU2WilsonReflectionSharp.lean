/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/

import YangMills.OS.SU2WilsonReflectionKernel
import YangMills.ClayCore.SchurFundamentalOrthogonality

/-!
# Sharp SU(2) Wilson character gate

This file isolates the degree-zero and degree-one calculations for the
fundamental character from the positive Taylor tail.
-/

noncomputable section

open Matrix Complex MeasureTheory
open scoped BigOperators
open scoped Topology

namespace YangMills.OS

/-- The fundamental SU(2) character used by the sharp non-vacuity gate. -/
def su2TraceObservable (U : SU2) : ℂ :=
  Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)

theorem su2TraceObservable_continuous :
    Continuous su2TraceObservable :=
  continuous_trace_sub 2

/-- The constant Taylor mode vanishes exactly for the character observable. -/
theorem su2TraceObservable_haar_mean_zero :
    ∫ U : SU2, su2TraceObservable U ∂(sunHaarProb 2) = 0 := by
  simpa [su2TraceObservable] using
    (sunHaarProb_trace_complex_integral_zero 2 (by norm_num))

set_option maxHeartbeats 400000 in
/-- The trace of an SU(2) matrix is real. -/
theorem su2_trace_star_eq_trace (U : SU2) :
    star U.val.trace = U.val.trace := by
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp U.property
  have hunit : U.val * star U.val = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hmem.1
  have hdet : U.val.det = 1 := hmem.2
  have hadj : Matrix.adjugate U.val * U.val = 1 := by
    rw [Matrix.adjugate_mul, hdet, one_smul]
  have hstarAdj : star U.val = Matrix.adjugate U.val := by
    calc
      star U.val = 1 * star U.val := by rw [one_mul]
      _ = (Matrix.adjugate U.val * U.val) * star U.val := by rw [hadj]
      _ = Matrix.adjugate U.val * (U.val * star U.val) := by
        rw [mul_assoc]
      _ = Matrix.adjugate U.val := by rw [hunit, mul_one]
  have htraceAdj : (Matrix.adjugate U.val).trace = U.val.trace := by
    rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
    simp [Matrix.trace_fin_two]
    abel
  calc
    star U.val.trace = (star U.val).trace :=
      (trace_star_eq_star_trace U.val).symm
    _ = (Matrix.adjugate U.val).trace := congrArg Matrix.trace hstarAdj
    _ = U.val.trace := htraceAdj

/-- The degree-one feature moment of the fundamental character. -/
def su2TraceEntryMoment (i j : Fin 2) : ℂ :=
  ∫ U : SU2, star (su2TraceObservable U) * U.val i j
    ∂(sunHaarProb 2)

set_option maxHeartbeats 400000 in
/-- Fundamental Schur orthogonality gives the character-entry moment
`δᵢⱼ / 2`. -/
theorem su2TraceEntryMoment_eq (i j : Fin 2) :
    su2TraceEntryMoment i j =
      if i = j then (1 : ℂ) / 2 else 0 := by
  unfold su2TraceEntryMoment su2TraceObservable
  change (∫ U : SU2, star (∑ k : Fin 2, U.val k k) * U.val i j
      ∂(sunHaarProb 2)) = _
  calc
    (∫ U : SU2, star (∑ k : Fin 2, U.val k k) * U.val i j
        ∂(sunHaarProb 2)) =
        ∫ U : SU2, ∑ k : Fin 2, U.val i j * star (U.val k k)
          ∂(sunHaarProb 2) := by
            congr 1
            funext U
            have hstar :
                star (∑ k : Fin 2, U.val k k) =
                  ∑ k : Fin 2, star (U.val k k) :=
              map_sum (starRingEnd ℂ) _ _
            rw [hstar]
            simp_rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = ∑ k : Fin 2,
        ∫ U : SU2, U.val i j * star (U.val k k)
          ∂(sunHaarProb 2) := by
            apply integral_finset_sum
            intro k hk
            have hc : Continuous (fun U : SU2 =>
                U.val i j * star (U.val k k)) :=
              (YangMills.ClayCore.continuous_val_entry i j).mul
                (YangMills.ClayCore.continuous_val_entry k k).star
            exact hc.integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
    _ = if i = j then (1 : ℂ) / 2 else 0 := by
      fin_cases i <;> fin_cases j <;>
        rw [Fin.sum_univ_two,
          YangMills.ClayCore.sunHaarProb_fundamental_entry_orthogonality,
          YangMills.ClayCore.sunHaarProb_fundamental_entry_orthogonality] <;>
        norm_num

set_option maxHeartbeats 400000 in
/-- Linearity of the Haar quadratic form in a finite sum of continuous
kernels. This is the only analytic bookkeeping needed for the finite head. -/
theorem kernelIntegralForm_finset_sum
    {ι : Type*} (s : Finset ι) (K : ι → SU2 → SU2 → ℂ)
    (F : SU2 → ℂ)
    (hK : ∀ a ∈ s, Continuous (Function.uncurry (K a)))
    (hF : Continuous F) :
    kernelIntegralForm (sunHaarProb 2)
        (fun x y => ∑ a ∈ s, K a x y) F =
      ∑ a ∈ s,
        kernelIntegralForm (sunHaarProb 2) (K a) F := by
  let μ : Measure SU2 := sunHaarProb 2
  have hinner_integrable (a : ι) (ha : a ∈ s) (x : SU2) :
      Integrable (fun y =>
        star (F x) * K a x y * F y) μ := by
    have hsection : Continuous (fun y : SU2 => K a x y) := by
      simpa [Function.uncurry] using
        (hK a ha).comp (continuous_const.prodMk continuous_id)
    exact ((continuous_const.mul hsection).mul hF).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have houter_integrable (a : ι) (ha : a ∈ s) :
      Integrable (fun x =>
        ∫ y, star (F x) * K a x y * F y ∂μ) μ := by
    have hc : Continuous (fun p : SU2 × SU2 =>
        star (F p.1) * K a p.1 p.2 * F p.2) := by
      exact (((hF.star.comp continuous_fst).mul (hK a ha)).mul
        (hF.comp continuous_snd))
    have hci : ContinuousOn
        (fun x => ∫ y, star (F x) * K a x y * F y ∂μ)
        Set.univ := by
      refine continuousOn_integral_of_compact_support
        (μ := μ) (s := Set.univ) (k := Set.univ) isCompact_univ
        ?_ ?_
      · simpa [Function.uncurry] using hc
      · intro p x hp hx
        simp at hx
    exact (continuousOn_univ.mp hci).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold kernelIntegralForm
  change (∫ x, ∫ y,
      star (F x) * (∑ a ∈ s, K a x y) * F y ∂μ ∂μ) = _
  calc
    (∫ x, ∫ y,
        star (F x) * (∑ a ∈ s, K a x y) * F y ∂μ ∂μ) =
        ∫ x, ∑ a ∈ s,
          (∫ y, star (F x) * K a x y * F y ∂μ) ∂μ := by
      congr 1
      funext x
      calc
        (∫ y, star (F x) * (∑ a ∈ s, K a x y) * F y ∂μ) =
            ∫ y, ∑ a ∈ s,
              star (F x) * K a x y * F y ∂μ := by
          congr 1
          funext y
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = ∑ a ∈ s,
            ∫ y, star (F x) * K a x y * F y ∂μ := by
          apply integral_finset_sum
          intro a ha
          exact hinner_integrable a ha x
    _ = ∑ a ∈ s,
        ∫ x, ∫ y, star (F x) * K a x y * F y ∂μ ∂μ := by
      apply integral_finset_sum
      intro a ha
      exact houter_integrable a ha
    _ = ∑ a ∈ s,
        kernelIntegralForm (sunHaarProb 2) (K a) F := by
      rfl

set_option maxHeartbeats 400000 in
/-- The real-part definition of the exponent agrees, on SU(2), with the
four-entry Hermitian dot product. -/
theorem su2WilsonExponentKernel_eq_entry_sum (β : ℝ) (x y : SU2) :
    su2WilsonExponentKernel β x y =
      ((β / 2 : ℝ) : ℂ) *
        ∑ i : Fin 2, ∑ j : Fin 2, x.val i j * star (y.val i j) := by
  have hreal :
      ((Matrix.trace (((x * y⁻¹ : SU2) :
          Matrix (Fin 2) (Fin 2) ℂ))).re : ℂ) =
        Matrix.trace (((x * y⁻¹ : SU2) :
          Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [Complex.re_eq_add_conj]
    have hs :
        (starRingEnd ℂ)
            (Matrix.trace (((x * y⁻¹ : SU2) :
              Matrix (Fin 2) (Fin 2) ℂ))) =
          Matrix.trace (((x * y⁻¹ : SU2) :
            Matrix (Fin 2) (Fin 2) ℂ)) :=
      su2_trace_star_eq_trace (x * y⁻¹)
    rw [hs]
    ring
  unfold su2WilsonExponentKernel
  push_cast
  have hreal' :
      ((Matrix.trace
          ((x.val * (y⁻¹ : SU2).val) :
            Matrix (Fin 2) (Fin 2) ℂ)).re : ℂ) =
        Matrix.trace
          ((x.val * (y⁻¹ : SU2).val) :
            Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa using hreal
  rw [hreal']
  have hentries :
      Matrix.trace
          ((x.val * (y⁻¹ : SU2).val) :
            Matrix (Fin 2) (Fin 2) ℂ) =
        ∑ i : Fin 2, ∑ j : Fin 2,
          x.val i j * star (y.val i j) := by
    simpa using su2_trace_mul_inv_eq_sum_entries x y
  rw [hentries]

/-- The entry moment for a general continuous observable. -/
def su2EntryMoment (F : SU2 → ℂ) (i j : Fin 2) : ℂ :=
  ∫ U : SU2, star (F U) * U.val i j ∂(sunHaarProb 2)

set_option maxHeartbeats 400000 in
/-- Exact factorization of one matrix-entry rank-one summand. -/
theorem kernelIntegralForm_entry_eq
    (β : ℝ) (F : SU2 → ℂ) (i j : Fin 2) :
    kernelIntegralForm (sunHaarProb 2)
        (fun x y => ((β / 2 : ℝ) : ℂ) *
          x.val i j * star (y.val i j)) F =
      ((β / 2 : ℝ) : ℂ) * su2EntryMoment F i j *
        star (su2EntryMoment F i j) := by
  let μ : Measure SU2 := sunHaarProb 2
  let A : ℂ := su2EntryMoment F i j
  have hconj :
      (∫ y : SU2, star (y.val i j) * F y ∂μ) = star A := by
    change (∫ y : SU2, star (y.val i j) * F y ∂μ) =
      star (∫ y : SU2, star (F y) * y.val i j ∂μ)
    calc
      (∫ y : SU2, star (y.val i j) * F y ∂μ) =
          ∫ y : SU2, star (star (F y) * y.val i j) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp [mul_comm]
      _ = star (∫ y : SU2, star (F y) * y.val i j ∂μ) :=
        integral_conj
  unfold kernelIntegralForm
  change (∫ x : SU2, ∫ y : SU2,
      star (F x) *
        (((β / 2 : ℝ) : ℂ) * x.val i j * star (y.val i j)) *
        F y ∂μ ∂μ) = _
  calc
    (∫ x : SU2, ∫ y : SU2,
        star (F x) *
          (((β / 2 : ℝ) : ℂ) * x.val i j * star (y.val i j)) *
          F y ∂μ ∂μ) =
        ∫ x : SU2,
          (((β / 2 : ℝ) : ℂ) * (star (F x) * x.val i j)) *
            (∫ y : SU2, star (y.val i j) * F y ∂μ) ∂μ := by
      congr 1
      funext x
      let c : ℂ := ((β / 2 : ℝ) : ℂ) *
        (star (F x) * x.val i j)
      calc
        (∫ y : SU2, star (F x) *
            (((β / 2 : ℝ) : ℂ) * x.val i j * star (y.val i j)) *
            F y ∂μ) =
            ∫ y : SU2, c * (star (y.val i j) * F y) ∂μ := by
          congr 1
          funext y
          dsimp [c]
          ring
        _ = c * (∫ y : SU2, star (y.val i j) * F y ∂μ) := by
          exact integral_const_mul (μ := μ) c
            (fun y : SU2 => star (y.val i j) * F y)
        _ = (((β / 2 : ℝ) : ℂ) * (star (F x) * x.val i j)) *
            (∫ y : SU2, star (y.val i j) * F y ∂μ) := by
          rfl
    _ = ∫ x : SU2,
        (((β / 2 : ℝ) : ℂ) * (star (F x) * x.val i j)) *
          star A ∂μ := by rw [hconj]
    _ = ((β / 2 : ℝ) : ℂ) *
        (∫ x : SU2, star (F x) * x.val i j ∂μ) * star A := by
      calc
        (∫ x : SU2,
            (((β / 2 : ℝ) : ℂ) * (star (F x) * x.val i j)) *
              star A ∂μ) =
            (∫ x : SU2,
              ((β / 2 : ℝ) : ℂ) * (star (F x) * x.val i j) ∂μ) *
              star A := by
          exact integral_mul_const _ _
        _ = (((β / 2 : ℝ) : ℂ) *
            (∫ x : SU2, star (F x) * x.val i j ∂μ)) * star A := by
          exact congrArg (fun z : ℂ => z * star A)
            (integral_const_mul (μ := μ) ((β / 2 : ℝ) : ℂ)
              (fun x : SU2 => star (F x) * x.val i j))
    _ = ((β / 2 : ℝ) : ℂ) * su2EntryMoment F i j *
        star (su2EntryMoment F i j) := by rfl

set_option maxHeartbeats 400000 in
/-- Exact degree-one quadratic form, obtained from four complex entry moments.
No positive-presentation machinery is used in this calculation. -/
theorem kernelIntegralForm_exponentKernel_eq
    (β : ℝ) (F : SU2 → ℂ) (hF : Continuous F) :
    kernelIntegralForm (sunHaarProb 2)
        (su2WilsonExponentKernel β) F =
      ((β / 2 : ℝ) : ℂ) *
        ∑ i : Fin 2, ∑ j : Fin 2,
          su2EntryMoment F i j * star (su2EntryMoment F i j) := by
  let K : (Fin 2 × Fin 2) → SU2 → SU2 → ℂ :=
    fun p x y => ((β / 2 : ℝ) : ℂ) *
      x.val p.1 p.2 * star (y.val p.1 p.2)
  have hK (p : Fin 2 × Fin 2) :
      Continuous (Function.uncurry (K p)) := by
    unfold K Function.uncurry
    exact (continuous_const.mul
      ((YangMills.ClayCore.continuous_val_entry p.1 p.2).comp
        continuous_fst)).mul
      ((YangMills.ClayCore.continuous_val_entry p.1 p.2).star.comp
        continuous_snd)
  have hkernel (x y : SU2) :
      su2WilsonExponentKernel β x y =
        ∑ p : Fin 2 × Fin 2, K p x y := by
    rw [su2WilsonExponentKernel_eq_entry_sum]
    unfold K
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    simp
    ring
  calc
    kernelIntegralForm (sunHaarProb 2)
        (su2WilsonExponentKernel β) F =
        kernelIntegralForm (sunHaarProb 2)
          (fun x y => ∑ p ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
            K p x y) F := by
      congr 1
      funext x y
      simpa using hkernel x y
    _ = ∑ p ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
        kernelIntegralForm (sunHaarProb 2) (K p) F := by
      apply kernelIntegralForm_finset_sum
      · intro p hp
        exact hK p
      · exact hF
    _ = ∑ p : Fin 2 × Fin 2,
        (((β / 2 : ℝ) : ℂ) * su2EntryMoment F p.1 p.2 *
          star (su2EntryMoment F p.1 p.2)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact kernelIntegralForm_entry_eq β F p.1 p.2
    _ = ((β / 2 : ℝ) : ℂ) *
        ∑ i : Fin 2, ∑ j : Fin 2,
          su2EntryMoment F i j * star (su2EntryMoment F i j) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

set_option maxHeartbeats 400000 in
/-- The fundamental character extracts exactly the `β/4` degree-one
contribution. -/
theorem su2Trace_degreeOne_eq (β : ℝ) :
    kernelIntegralForm (sunHaarProb 2)
        (su2WilsonExponentKernel β) su2TraceObservable =
      ((β / 4 : ℝ) : ℂ) := by
  rw [kernelIntegralForm_exponentKernel_eq β su2TraceObservable
    su2TraceObservable_continuous]
  have hm (i j : Fin 2) :
      su2EntryMoment su2TraceObservable i j =
        if i = j then (1 : ℂ) / 2 else 0 := by
    exact su2TraceEntryMoment_eq i j
  have hhalf :
      (starRingEnd ℂ) ((1 : ℂ) / 2) = (1 : ℂ) / 2 := by
    have heq : (1 : ℂ) / 2 = (((1 : ℝ) / 2 : ℝ) : ℂ) := by
      norm_num
    rw [heq, Complex.conj_ofReal]
  have hhalf' : star ((1 : ℂ) / 2) = (1 : ℂ) / 2 := hhalf
  have hm00 : su2EntryMoment su2TraceObservable 0 0 = (1 : ℂ) / 2 := by
    simpa using hm 0 0
  have hm01 : su2EntryMoment su2TraceObservable 0 1 = 0 := by
    simpa using hm 0 1
  have hm10 : su2EntryMoment su2TraceObservable 1 0 = 0 := by
    simpa using hm 1 0
  have hm11 : su2EntryMoment su2TraceObservable 1 1 = (1 : ℂ) / 2 := by
    simpa using hm 1 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.sum_univ_two]
  rw [hm00, hm01, hm10, hm11, hhalf']
  simp
  ring

set_option maxHeartbeats 400000 in
/-- Binary linearity, derived from the certified finite-sum lemma. -/
theorem kernelIntegralForm_add
    (K L : SU2 → SU2 → ℂ) (F : SU2 → ℂ)
    (hK : Continuous (Function.uncurry K))
    (hL : Continuous (Function.uncurry L))
    (hF : Continuous F) :
    kernelIntegralForm (sunHaarProb 2) (fun x y => K x y + L x y) F =
      kernelIntegralForm (sunHaarProb 2) K F +
        kernelIntegralForm (sunHaarProb 2) L F := by
  let M : Bool → SU2 → SU2 → ℂ := fun b => cond b L K
  have hM : ∀ b ∈ (Finset.univ : Finset Bool),
      Continuous (Function.uncurry (M b)) := by
    intro b hb
    cases b <;> simp [M, hK, hL]
  simpa [M, add_comm] using
    (kernelIntegralForm_finset_sum
      (Finset.univ : Finset Bool) M F hM hF)

set_option maxHeartbeats 400000 in
/-- The two-term Taylor head is pointwise `1 + K₁`. -/
theorem su2WilsonTaylorKernel_two (β : ℝ) (x y : SU2) :
    su2WilsonTaylorKernel β 2 x y =
      1 + su2WilsonExponentKernel β x y := by
  norm_num [su2WilsonTaylorKernel, su2WilsonTaylorCoeff,
    Finset.sum_range_succ]

set_option maxHeartbeats 400000 in
/-- The constant mode vanishes exactly on the fundamental character. -/
theorem su2Trace_constantKernel_eq_zero :
    kernelIntegralForm (sunHaarProb 2)
        (fun _ _ : SU2 => (1 : ℂ)) su2TraceObservable = 0 := by
  unfold kernelIntegralForm
  have hinner (x : SU2) :
      (∫ y : SU2,
        star (su2TraceObservable x) * 1 * su2TraceObservable y
          ∂(sunHaarProb 2)) = 0 := by
    simp only [mul_one]
    calc
      (∫ y : SU2,
          star (su2TraceObservable x) * su2TraceObservable y
            ∂(sunHaarProb 2)) =
          star (su2TraceObservable x) *
            (∫ y : SU2, su2TraceObservable y ∂(sunHaarProb 2)) := by
        exact integral_const_mul (μ := sunHaarProb 2)
          (star (su2TraceObservable x)) su2TraceObservable
      _ = 0 := by rw [su2TraceObservable_haar_mean_zero, mul_zero]
  change (∫ x : SU2, ∫ y : SU2,
    star (su2TraceObservable x) * 1 * su2TraceObservable y
      ∂(sunHaarProb 2) ∂(sunHaarProb 2)) = 0
  have hfun :
      (fun x : SU2 => ∫ y : SU2,
        star (su2TraceObservable x) * 1 * su2TraceObservable y
          ∂(sunHaarProb 2)) = fun _ => 0 :=
    funext hinner
  rw [hfun]
  simp

set_option maxHeartbeats 400000 in
/-- Brick 3: the finite Taylor head already pairs with the fundamental
character to exactly `β/4`. -/
theorem su2Trace_taylorTwo_eq (β : ℝ) :
    kernelIntegralForm (sunHaarProb 2)
        (su2WilsonTaylorKernel β 2) su2TraceObservable =
      ((β / 4 : ℝ) : ℂ) := by
  have hk :
      su2WilsonTaylorKernel β 2 =
        fun x y => (fun _ _ : SU2 => (1 : ℂ)) x y +
          su2WilsonExponentKernel β x y := by
    funext x y
    exact su2WilsonTaylorKernel_two β x y
  rw [hk, kernelIntegralForm_add]
  · rw [su2Trace_constantKernel_eq_zero, su2Trace_degreeOne_eq]
    simp
  · fun_prop
  · exact su2WilsonExponentKernel_continuous β
  · exact su2TraceObservable_continuous

/-- The Taylor tail beginning at degree two. -/
def su2WilsonTaylorTailKernel (β : ℝ) (N : ℕ) (x y : SU2) : ℂ :=
  ∑ n ∈ Finset.range N,
    (su2WilsonTaylorCoeff (n + 2) : ℂ) *
      su2WilsonExponentKernel β x y ^ (n + 2)

set_option maxHeartbeats 400000 in
/-- Every finite tail beginning at degree two retains an explicit positive
presentation. -/
theorem su2WilsonTaylorTail_hasContinuousPositivePresentation
    (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) :
    HasContinuousPositivePresentation (su2WilsonTaylorTailKernel β N) := by
  have hbase :
      HasContinuousPositivePresentation (su2WilsonExponentKernel β) :=
    ⟨SU2WilsonFeatureIndex, inferInstance, su2WilsonLinearCoeff β,
      su2WilsonFeature, su2WilsonExponent_finiteRank β hβ⟩
  unfold su2WilsonTaylorTailKernel
  apply HasContinuousPositivePresentation.finset_sum
  intro n hn
  exact (hbase.pow (n + 2)).scale (su2WilsonTaylorCoeff (n + 2))
    (su2WilsonTaylorCoeff_nonneg (n + 2))

set_option maxHeartbeats 400000 in
/-- Hence the finite degree-at-least-two tail has non-negative Haar
quadratic form. -/
theorem su2WilsonTaylorTail_isHaarPSDKernel
    (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) :
    IsHaarPSDKernel (sunHaarProb 2)
      (su2WilsonTaylorTailKernel β N) := by
  rcases
      su2WilsonTaylorTail_hasContinuousPositivePresentation β hβ N with
    ⟨ι, hι, c, φ, h⟩
  letI : Fintype ι := hι
  exact isHaarPSDKernel_of_continuousFiniteRank (sunHaarProb 2) h

set_option maxHeartbeats 400000 in
/-- Exact decomposition of a shifted truncation into its two-term head and
the positive tail. -/
theorem su2WilsonTaylorKernel_add_two (β : ℝ) (N : ℕ) (x y : SU2) :
    su2WilsonTaylorKernel β (N + 2) x y =
      su2WilsonTaylorKernel β 2 x y +
        su2WilsonTaylorTailKernel β N x y := by
  unfold su2WilsonTaylorKernel su2WilsonTaylorTailKernel
  rw [Nat.add_comm N 2, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Nat.add_comm 2 n]

set_option maxHeartbeats 400000 in
/-- Every shifted truncation is bounded below by its exact `β/4` head when
tested on the fundamental character. -/
theorem su2Trace_taylor_lower
    (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) :
    β / 4 ≤
      (kernelIntegralForm (sunHaarProb 2)
        (su2WilsonTaylorKernel β (N + 2)) su2TraceObservable).re := by
  rcases su2WilsonTaylorTail_isHaarPSDKernel β hβ N
      su2TraceObservable su2TraceObservable_continuous with
    ⟨r, hr, hr_eq⟩
  have htail_cont :
      Continuous (Function.uncurry (su2WilsonTaylorTailKernel β N)) :=
    (su2WilsonTaylorTail_hasContinuousPositivePresentation β hβ N).continuous_uncurry
  have hkernel :
      su2WilsonTaylorKernel β (N + 2) =
        fun x y => su2WilsonTaylorKernel β 2 x y +
          su2WilsonTaylorTailKernel β N x y := by
    funext x y
    exact su2WilsonTaylorKernel_add_two β N x y
  have hform :
      kernelIntegralForm (sunHaarProb 2)
          (su2WilsonTaylorKernel β (N + 2)) su2TraceObservable =
        kernelIntegralForm (sunHaarProb 2)
            (su2WilsonTaylorKernel β 2) su2TraceObservable +
          kernelIntegralForm (sunHaarProb 2)
            (su2WilsonTaylorTailKernel β N) su2TraceObservable := by
    rw [hkernel]
    exact kernelIntegralForm_add
      (su2WilsonTaylorKernel β 2)
      (su2WilsonTaylorTailKernel β N) su2TraceObservable
      (su2WilsonTaylorKernel_continuous β 2) htail_cont
      su2TraceObservable_continuous
  rw [hform, su2Trace_taylorTwo_eq, hr_eq]
  simp only [add_re, ofReal_re]
  linarith

set_option maxHeartbeats 400000 in
/-- Sharp non-vacuity gate for the exact Wilson crossing kernel. The lower
bound is transported from the exact degree-one head through the non-negative
Taylor tail and the already certified dominated-convergence limit. -/
theorem su2Trace_crossing_lower
    (β : ℝ) (hβ : 0 ≤ β) :
    β / 4 ≤
      (kernelIntegralForm (sunHaarProb 2)
        (su2WilsonCrossingKernel β) su2TraceObservable).re := by
  let q : ℕ → ℂ := fun N =>
    kernelIntegralForm (sunHaarProb 2)
      (su2WilsonTaylorKernel β N) su2TraceObservable
  let qLimit : ℂ :=
    kernelIntegralForm (sunHaarProb 2)
      (su2WilsonCrossingKernel β) su2TraceObservable
  have hq : Filter.Tendsto q Filter.atTop (𝓝 qLimit) := by
    simpa [q, qLimit] using
      su2WilsonKernelIntegralForm_tendsto β hβ
        su2TraceObservable su2TraceObservable_continuous
  have hq_shift :
      Filter.Tendsto (fun N => q (N + 2)) Filter.atTop (𝓝 qLimit) :=
    (Filter.tendsto_add_atTop_iff_nat 2).2 hq
  have hq_re :
      Filter.Tendsto (fun N => (q (N + 2)).re)
        Filter.atTop (𝓝 qLimit.re) :=
    (Complex.continuous_re.tendsto qLimit).comp hq_shift
  have hlower (N : ℕ) : β / 4 ≤ (q (N + 2)).re := by
    exact su2Trace_taylor_lower β hβ N
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hq_re
    (Filter.Eventually.of_forall hlower)

end YangMills.OS
