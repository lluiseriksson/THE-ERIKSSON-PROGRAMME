/-
  YangMills/ClayCore/SchurL25.lean

  Milestone L2.5:  ∫ |tr U|² dHaar ≤ N  on SU(N).

  Combines:
    * Step A + Step B  — off-diagonal Haar integral vanishes.
    * L2.4 pointwise identities.
    * Mathlib `entry_norm_bound_of_unitary`: pointwise `|U_{ii}| ≤ 1`.

  Status: no sorry, no new axioms.
  Oracle must remain [propext, Classical.choice, Quot.sound].
-/
import YangMills.ClayCore.SchurOffDiagonal
import YangMills.ClayCore.SchurNormSquared
import YangMills.P8_PhysicalGap.SUN_Compact

noncomputable section
open MeasureTheory Matrix Complex Finset
open scoped BigOperators

namespace YangMills.ClayCore

variable {N : ℕ} [NeZero N]

/-! ### Continuity / integrability of matrix entries on `SU(N)` -/

lemma continuous_val_entry (i j : Fin N) :
    Continuous (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ => U.val i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

lemma continuous_entry_mul_star (i j : Fin N) :
    Continuous (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      U.val i i * star (U.val j j)) :=
  (continuous_val_entry i i).mul (continuous_star.comp (continuous_val_entry j j))

lemma entry_mul_star_integrable (i j : Fin N) :
    Integrable (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      U.val i i * star (U.val j j)) (sunHaarProb N) :=
  (continuous_entry_mul_star i j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma val_normSq_integrable (i : Fin N) :
    Integrable (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      (Complex.normSq (U.val i i) : ℝ)) (sunHaarProb N) :=
  (Complex.continuous_normSq.comp (continuous_val_entry i i)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-! ### `Complex.normSq = ‖·‖²` via the RCLike API -/

lemma complex_normSq_eq_norm_sq (z : ℂ) : Complex.normSq z = ‖z‖ ^ 2 := by
  show RCLike.normSq z = ‖z‖ ^ 2
  exact RCLike.normSq_eq_def' _

/-! ### Pointwise bound `|U_{ii}|² ≤ 1` -/

lemma normSq_val_diag_le_one (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (i : Fin N) :
    Complex.normSq (U.val i i) ≤ 1 := by
  have hU : U.val ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.property).1
  have hnorm : ‖U.val i i‖ ≤ 1 := entry_norm_bound_of_unitary hU i i
  have h0 : (0 : ℝ) ≤ ‖U.val i i‖ := norm_nonneg _
  have hsq : ‖U.val i i‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ h0 hnorm 2
  rw [complex_normSq_eq_norm_sq]
  linarith

lemma diag_normSq_integral_le_one (i : Fin N) :
    (∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N)) ≤ 1 := by
  calc ∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N)
      ≤ ∫ _U, (1 : ℝ) ∂(sunHaarProb N) :=
        MeasureTheory.integral_mono_ae (val_normSq_integrable i) (integrable_const 1)
          (ae_of_all _ (fun U => normSq_val_diag_le_one U i))
    _ = 1 := by simp

/-! ### Frobenius expansion of `tr U · conj(tr U)` -/

lemma trace_mul_conj_trace_eq_double_sum (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    U.val.trace * star U.val.trace =
      ∑ i : Fin N, ∑ j : Fin N, U.val i i * star (U.val j j) := by
  have htr : U.val.trace = ∑ i : Fin N, U.val i i := by
    simp [Matrix.trace, Matrix.diag_apply]
  have hstar : star U.val.trace = ∑ j : Fin N, star (U.val j j) := by
    rw [htr]; exact map_sum (starRingEnd ℂ) _ _
  rw [hstar, htr, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-! ### Off-diagonal collapse -/

lemma inner_sum_collapse_to_diag (i : Fin N) :
    (∑ j : Fin N, ∫ U, U.val i i * star (U.val j j) ∂(sunHaarProb N))
      = ∫ U, U.val i i * star (U.val i i) ∂(sunHaarProb N) := by
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    exact sunHaarProb_offdiag_integral_zero hji.symm
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### Main complex identity -/

lemma integral_trace_mul_conj_trace_eq_sum :
    (∫ U, U.val.trace * star U.val.trace ∂(sunHaarProb N))
      = ∑ i : Fin N, ∫ U, U.val i i * star (U.val i i) ∂(sunHaarProb N) := by
  have hpt : ∀ U : Matrix.specialUnitaryGroup (Fin N) ℂ,
      U.val.trace * star U.val.trace =
        ∑ i : Fin N, ∑ j : Fin N, U.val i i * star (U.val j j) :=
    trace_mul_conj_trace_eq_double_sum
  calc (∫ U, U.val.trace * star U.val.trace ∂(sunHaarProb N))
      = ∫ U, ∑ i : Fin N, ∑ j : Fin N, U.val i i * star (U.val j j) ∂(sunHaarProb N) :=
          MeasureTheory.integral_congr_ae (ae_of_all _ hpt)
    _ = ∑ i : Fin N, ∫ U, ∑ j : Fin N, U.val i i * star (U.val j j) ∂(sunHaarProb N) :=
          MeasureTheory.integral_finset_sum _ fun i _ =>
            MeasureTheory.integrable_finset_sum _ fun j _ => entry_mul_star_integrable i j
    _ = ∑ i : Fin N, ∑ j : Fin N, ∫ U, U.val i i * star (U.val j j) ∂(sunHaarProb N) :=
          Finset.sum_congr rfl fun i _ =>
            MeasureTheory.integral_finset_sum _ fun j _ => entry_mul_star_integrable i j
    _ = ∑ i : Fin N, ∫ U, U.val i i * star (U.val i i) ∂(sunHaarProb N) :=
          Finset.sum_congr rfl fun i _ => inner_sum_collapse_to_diag i

/-! ### Diagonal integrals via `Complex.normSq` -/

lemma diag_integral_ofReal (i : Fin N) :
    (∫ U, U.val i i * star (U.val i i) ∂(sunHaarProb N))
      = ((∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N) : ℝ) : ℂ) := by
  have hpt : ∀ U : Matrix.specialUnitaryGroup (Fin N) ℂ,
      U.val i i * star (U.val i i) = ((Complex.normSq (U.val i i) : ℝ) : ℂ) :=
    fun U => Complex.mul_conj (U.val i i)
  rw [MeasureTheory.integral_congr_ae (ae_of_all _ hpt)]
  exact integral_ofReal

/-! ### Main theorem: ∫ |tr U|² dHaar ≤ N -/

theorem sunHaarProb_trace_normSq_integral_le :
    (∫ U, (Complex.normSq U.val.trace : ℝ) ∂(sunHaarProb N)) ≤ (N : ℝ) := by
  have hpt_trace : ∀ U : Matrix.specialUnitaryGroup (Fin N) ℂ,
      U.val.trace * star U.val.trace = ((Complex.normSq U.val.trace : ℝ) : ℂ) :=
    fun U => Complex.mul_conj U.val.trace
  have hC :
      ((∫ U, (Complex.normSq U.val.trace : ℝ) ∂(sunHaarProb N) : ℝ) : ℂ)
        = ∑ i : Fin N, ((∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N) : ℝ) : ℂ) := by
    have step1 :
        ((∫ U, (Complex.normSq U.val.trace : ℝ) ∂(sunHaarProb N) : ℝ) : ℂ)
          = ∫ U, ((Complex.normSq U.val.trace : ℝ) : ℂ) ∂(sunHaarProb N) :=
      integral_ofReal.symm
    rw [step1]
    rw [show (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
            ((Complex.normSq U.val.trace : ℝ) : ℂ))
          = fun U => U.val.trace * star U.val.trace from by
        funext U; exact (hpt_trace U).symm]
    rw [integral_trace_mul_conj_trace_eq_sum]
    exact Finset.sum_congr rfl fun i _ => diag_integral_ofReal i
  have hR : (∫ U, (Complex.normSq U.val.trace : ℝ) ∂(sunHaarProb N))
        = ∑ i : Fin N, ∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N) := by
    have hRHS :
        (∑ i : Fin N, ((∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N) : ℝ) : ℂ))
          = (((∑ i : Fin N, ∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N)) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hRHS] at hC
    exact_mod_cast hC
  rw [hR]
  calc ∑ i : Fin N, ∫ U, (Complex.normSq (U.val i i) : ℝ) ∂(sunHaarProb N)
      ≤ ∑ _i : Fin N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => diag_normSq_integral_le_one i
    _ = (N : ℝ) := by simp

end YangMills.ClayCore

end
