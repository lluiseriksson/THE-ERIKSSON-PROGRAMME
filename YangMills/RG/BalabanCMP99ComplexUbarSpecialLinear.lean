import YangMills.RG.BalabanCMP116DeterminantNearLog
import YangMills.RG.MatrixDetExpSkewAdjoint
import YangMills.RG.MatrixRealization
import YangMills.RG.NearLogDeviationBudget

/-!
# The analytic CMP99 Ubar factor in `SL(N,C)`

The lattice deviation and its gauge-covariance law in `Ubar.lean` are already
group-generic.  What cannot be reused from the physical `SU(N)` constructor is
the skew-adjoint closure.  This file isolates the correct complex replacement:
determinant one plus the same explicit no-winding budget makes every principal
Mercator logarithm traceless, without a unitarity hypothesis.  The weighted
exponential can therefore be packaged in `SL(N,C)`.

This is only the algebraic one-block closure.  It constructs no localized
background chain, source radius producer, analytic average or Eq. (3.37)
tower, and it does not move a terminal counter.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- The defining matrix representation of `SL(N,C)` as matrix units. -/
instance instMatrixRealizationSpecialLinear :
    MatrixRealization (Matrix.SpecialLinearGroup (Fin Nc) ℂ)
      (Matrix (Fin Nc) (Fin Nc) ℂ) where
  rep := Matrix.SpecialLinearGroup.toGL

local instance cmp99ComplexUbarSpecialLinearMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Determinant one quantizes the trace of the principal Mercator logarithm;
no unitarity or skew-adjointness is needed for this implication. -/
theorem matrixTraceQuantized_nearLog_sub_one_of_det_eq_one
    (D : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hD : ‖D - 1‖ < 1) (hdet : Matrix.det D = 1) :
    MatrixTraceQuantized (nearLog (D - 1)) := by
  have hexp : Complex.exp (Matrix.trace (nearLog (D - 1))) = 1 := by
    have hdetLog : Matrix.det (1 + (D - 1)) =
        Complex.exp (Matrix.trace (nearLog (D - 1))) := by
      rw [← exp_nearLog_eq_one_add hD]
      exact det_matrix_exp_eq_exp_trace (nearLog (D - 1))
    rw [← hdetLog]
    simpa using hdet
  rcases Complex.exp_eq_one_iff.mp hexp with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [hk]
  push_cast
  ring

/-- The strict no-winding budget selects the zero winding for an arbitrary
near-identity determinant-one complex matrix. -/
theorem trace_nearLog_sub_one_eq_zero_of_det_eq_one_of_noWinding
    (D : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hD : ‖D - 1‖ < 1) (hdet : Matrix.det D = 1)
    (hnoWinding : (Nc : ℝ) * ‖nearLog (D - 1)‖ < 2 * Real.pi) :
    Matrix.trace (nearLog (D - 1)) = 0 := by
  apply trace_eq_zero_of_quantized_of_norm_lt_two_pi _
    (matrixTraceQuantized_nearLog_sub_one_of_det_eq_one D hD hdet)
  calc
    ‖Matrix.trace (nearLog (D - 1))‖
        ≤ (Nc : ℝ) * ‖nearLog (D - 1)‖ :=
      norm_matrix_trace_le_card_mul_l2_opNorm _
    _ < 2 * Real.pi := hnoWinding

/-- The literal weighted analytic Ubar exponent for determinant-one complex
deviations.  Its coefficients remain real because the printed block average
has mass `M^{-d}`. -/
noncomputable def cmp99UbarSpecialLinearExponent {iota : Type*}
    (s : Finset iota) (w : iota → ℝ)
    (D : iota → Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  ∑ i ∈ s, w i •
    nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)

/-- Every summand is traceless by determinant one and the explicit local
no-winding budget; hence the complete analytic exponent is traceless. -/
theorem trace_cmp99UbarSpecialLinearExponent_eq_zero {iota : Type*}
    (s : Finset iota) (w : iota → ℝ)
    (D : iota → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi) :
    Matrix.trace (cmp99UbarSpecialLinearExponent s w D) = 0 := by
  unfold cmp99UbarSpecialLinearExponent
  rw [Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have htrace : Matrix.trace
      (nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) = 0 :=
    trace_nearLog_sub_one_eq_zero_of_det_eq_one_of_noWinding
      (D i : Matrix (Fin Nc) (Fin Nc) ℂ) (hD i hi) (D i).property
      (hnoWinding i hi)
  unfold Matrix.trace at htrace ⊢
  have htrace' : ∑ j,
      nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) j j = 0 := by
    simpa only [Matrix.diag] using htrace
  change ∑ j, (w i : ℂ) *
      nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) j j = 0
  rw [← Finset.mul_sum, htrace', mul_zero]

/-- Canonical determinant-one complex Ubar factor.  No unitarity statement is
true or used away from the real slice. -/
noncomputable def cmp99UbarSpecialLinearFactorOfNearIdentity {iota : Type*}
    (s : Finset iota) (w : iota → ℝ)
    (D : iota → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi) : Matrix.SpecialLinearGroup (Fin Nc) ℂ :=
  ⟨NormedSpace.exp (cmp99UbarSpecialLinearExponent s w D), by
    rw [det_matrix_exp_eq_exp_trace,
      trace_cmp99UbarSpecialLinearExponent_eq_zero s w D hD hnoWinding,
      Complex.exp_zero]⟩

@[simp] theorem cmp99UbarSpecialLinearFactorOfNearIdentity_coe
    {iota : Type*} (s : Finset iota) (w : iota → ℝ)
    (D : iota → Matrix.SpecialLinearGroup (Fin Nc) ℂ) (hD) (hnoWinding) :
    (cmp99UbarSpecialLinearFactorOfNearIdentity
        s w D hD hnoWinding : Matrix (Fin Nc) (Fin Nc) ℂ) =
      NormedSpace.exp (cmp99UbarSpecialLinearExponent s w D) :=
  rfl

/-- Complete one-block analytic Ubar value in `SL(N,C)`. -/
noncomputable def cmp99UbarSpecialLinearBlockOfNearIdentity {iota : Type*}
    (s : Finset iota) (w : iota → ℝ)
    (D : iota → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi)
    (coarse : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    Matrix.SpecialLinearGroup (Fin Nc) ℂ :=
  cmp99UbarSpecialLinearFactorOfNearIdentity s w D hD hnoWinding * coarse

@[simp] theorem cmp99UbarSpecialLinearBlockOfNearIdentity_coe
    {iota : Type*} (s : Finset iota) (w : iota → ℝ)
    (D : iota → Matrix.SpecialLinearGroup (Fin Nc) ℂ) (hD) (hnoWinding)
    (coarse : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    (cmp99UbarSpecialLinearBlockOfNearIdentity
        s w D hD hnoWinding coarse : Matrix (Fin Nc) (Fin Nc) ℂ) =
      NormedSpace.exp (cmp99UbarSpecialLinearExponent s w D) *
        (coarse : Matrix (Fin Nc) (Fin Nc) ℂ) :=
  rfl

/-- Budget-facing analytic factor.  The scalar budget generates both the
Mercator-ball and no-winding premises; no logarithm family is caller data. -/
noncomputable def cmp99UbarSpecialLinearFactorOfDeviationBudget {iota : Type*}
    (s : Finset iota) (w : iota → ℝ)
    (D : iota → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ) :
    Matrix.SpecialLinearGroup (Fin Nc) ℂ :=
  cmp99UbarSpecialLinearFactorOfNearIdentity s w D
    (fun i hi => B.nearIdentity _ (hdev i hi))
    (fun i hi => B.nearLog_noWinding _ (hdev i hi))

@[simp] theorem cmp99UbarSpecialLinearFactorOfDeviationBudget_coe
    {iota : Type*} (s : Finset iota) (w : iota → ℝ)
    (D : iota → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (B : MatrixNearLogNoWindingBudget Nc) (hdev) :
    (cmp99UbarSpecialLinearFactorOfDeviationBudget
        s w D B hdev : Matrix (Fin Nc) (Fin Nc) ℂ) =
      NormedSpace.exp (cmp99UbarSpecialLinearExponent s w D) :=
  rfl

/-- Complete budget-facing one-block analytic Ubar value. -/
noncomputable def cmp99UbarSpecialLinearBlockOfDeviationBudget {iota : Type*}
    (s : Finset iota) (w : iota → ℝ)
    (D : iota → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (coarse : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    Matrix.SpecialLinearGroup (Fin Nc) ℂ :=
  cmp99UbarSpecialLinearFactorOfDeviationBudget s w D B hdev * coarse

@[simp] theorem cmp99UbarSpecialLinearBlockOfDeviationBudget_coe
    {iota : Type*} (s : Finset iota) (w : iota → ℝ)
    (D : iota → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (B : MatrixNearLogNoWindingBudget Nc) (hdev)
    (coarse : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    (cmp99UbarSpecialLinearBlockOfDeviationBudget
        s w D B hdev coarse : Matrix (Fin Nc) (Fin Nc) ℂ) =
      NormedSpace.exp (cmp99UbarSpecialLinearExponent s w D) *
        (coarse : Matrix (Fin Nc) (Fin Nc) ℂ) :=
  rfl

end

end YangMills.RG
