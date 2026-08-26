import YangMills.RG.BalabanCMP99Eq351ExponentialAdjointRemainder
import YangMills.RG.BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# CMP99 (3.51): positive-bond adjoint expansion

This leaf combines the canonical positive-bond factorization with the exact
exponential-adjoint remainder.  The baseline-transported field, generator,
commutator and nonlinear remainder are all built internally.  It is only the
one-bond algebraic prerequisite of the later three-species Laplacian
regrouping; it proves no pointwise or operator-norm bound.
-/

namespace YangMills.RG

noncomputable section

open Matrix

variable {d N Nc : Nat} [NeZero N] [NeZero Nc]

/-- Matrix form of the exact positive-bond expansion used in (3.51).

The theorem deliberately exposes the same named generator that defines the
canonical perturbed link and specializes the already sealed nonlinear
remainder.  No caller-supplied perturbed background, commutator or remainder
appears in the statement. -/
theorem cmp99Eq351PhysicalComplexPerturbedPositiveAdjointMatrix_eq
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (b : PhysicalBond d N)
    (Z : SUNLieComplexCoord Nc) :
    let Y := cmp99Eq351PhysicalComplexPositiveGeneratorMatrix A eta b
    let X := cmp99SUNLieComplexCoordMatrixLM Nc
      (cmp99SpecialLinearAdjointCoordLM
        (cmp99SUNToSpecialLinear Nc (U (positiveEdgeOfPhysicalBond b))) Z)
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SpecialLinearAdjointCoordLM
          (cmp99Eq337PhysicalComplexPerturbedPositiveBondSL U A eta b) Z) =
      X + (Y * X - X * Y) +
        cmp99Eq351ExponentialAdjointRemainderCLM Y X := by
  dsimp only
  rw [cmp99Eq351PhysicalComplexPerturbedPositiveBondSL_eq_mul,
    cmp99SpecialLinearAdjointCoordLM_mul,
    cmp99SUNLieComplexCoordMatrixLM_specialLinearAdjoint,
    cmp99Eq351PhysicalComplexPositiveExponentSL_coe,
    cmp99Eq351PhysicalComplexPositiveExponentSL_inv_coe]
  simpa only [physicalMatrixExp] using
    cmp99Eq351_exponentialAdjoint_apply_eq_linear_add_remainder
      (cmp99Eq351PhysicalComplexPositiveGeneratorMatrix A eta b)
      (cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SpecialLinearAdjointCoordLM
          (cmp99SUNToSpecialLinear Nc (U (positiveEdgeOfPhysicalBond b))) Z))

end

end YangMills.RG
