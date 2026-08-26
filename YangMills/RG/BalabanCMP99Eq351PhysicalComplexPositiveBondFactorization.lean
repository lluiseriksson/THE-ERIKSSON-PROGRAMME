import YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointComposition
import YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice

/-!
PRE-VALIDATION: source present, `.olean` not yet materialized, and the result
has not yet been verified by the compiler or axiom oracle.

# CMP99 (3.50): exact positive-bond factorization

The perturbed positive link is factored inside `SL(N,C)` as the literal
source exponential times the compact background embedded in `SL(N,C)`.
No independently chosen perturbed background or exponential factor enters.
-/

namespace YangMills.RG

noncomputable section

open Matrix

variable {d N Nc : Nat} [NeZero N] [NeZero Nc]

/-- The determinant-one exponential appearing literally in
`exp(i eta A'(b)) U(b)`. -/
def cmp99Eq351PhysicalComplexPositiveExponentSL
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N) :
    Matrix.SpecialLinearGroup (Fin Nc) ℂ := by
  let Y : Matrix (Fin Nc) (Fin Nc) ℂ :=
    (((Complex.I : ℂ) * (eta : ℂ)) •
      cmp99Eq337PrintedComplexLieMatrix (A b))
  refine ⟨physicalMatrixExp Y, ?_⟩
  have htrace : Matrix.trace Y = 0 := by
    dsimp [Y]
    rw [cmp99Eq337PrintedComplexGenerator_eq, Matrix.trace_smul,
      cmp99SUNLieComplexCoordMatrixLM_trace, smul_zero]
  simpa [physicalMatrixExp, htrace] using
    det_matrix_exp_eq_exp_trace Y

@[simp] theorem cmp99Eq351PhysicalComplexPositiveExponentSL_coe
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N) :
    ((cmp99Eq351PhysicalComplexPositiveExponentSL A eta b :
        Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
      Matrix (Fin Nc) (Fin Nc) ℂ) =
      physicalMatrixExp
        ((((Complex.I : ℂ) * (eta : ℂ)) •
          cmp99Eq337PrintedComplexLieMatrix (A b))) :=
  rfl

/-- Exact group-level factorization of the canonical perturbed positive
bond.  This is the source identity used before expanding its adjoint action.
-/
theorem cmp99Eq351PhysicalComplexPerturbedPositiveBondSL_eq_mul
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N) :
    cmp99Eq337PhysicalComplexPerturbedPositiveBondSL U A eta b =
      cmp99Eq351PhysicalComplexPositiveExponentSL A eta b *
        cmp99SUNToSpecialLinear Nc (U (positiveEdgeOfPhysicalBond b)) := by
  apply Subtype.ext
  simp [cmp99Eq337PhysicalComplexPerturbedPositiveBondSL,
    cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix,
    cmp99SUNToSpecialLinear_coe]

end

end YangMills.RG
