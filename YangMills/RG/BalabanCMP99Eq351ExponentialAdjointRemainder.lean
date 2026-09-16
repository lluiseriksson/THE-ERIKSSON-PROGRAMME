import YangMills.RG.BalabanCMP98GAdConjugation

/-!
# CMP99 (3.51): internal exponential-adjoint remainder

The nonlinear third species in the printed Laplacian expansion is not a free
operator.  This leaf defines it as the exact remainder after subtracting the
identity and the first commutator from conjugation by `exp Y`.  The definition
is valid in a real Banach algebra and therefore applies to the complex matrix
model used by the source-specific Eq. (3.51) regrouping.

This module proves only the exact algebraic decomposition.  Its quadratic
norm bound and the physical substitution `Y = i eta A'(b)` remain separate
source-facing obligations.
-/

namespace YangMills.RG

noncomputable section

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Literal nonlinear remainder of the exponential adjoint action. -/
noncomputable def cmp99Eq351ExponentialAdjointRemainderCLM
    (Y : A) : A →L[ℝ] A :=
  cmp98TwoSidedMulCLM (NormedSpace.exp Y) (NormedSpace.exp (-Y)) -
    ContinuousLinearMap.id ℝ A - cmp98AdCLM Y

@[simp] theorem cmp99Eq351ExponentialAdjointRemainderCLM_apply
    (Y X : A) :
    cmp99Eq351ExponentialAdjointRemainderCLM Y X =
      NormedSpace.exp Y * X * NormedSpace.exp (-Y) - X -
        (Y * X - X * Y) := by
  simp [cmp99Eq351ExponentialAdjointRemainderCLM]

/-- Operator form of the exact identity `exp(ad Y) = 1 + ad Y + R₂(Y)`. -/
theorem cmp99Eq351_exponentialAdjoint_eq_id_add_ad_add_remainder
    (Y : A) :
    cmp98TwoSidedMulCLM (NormedSpace.exp Y) (NormedSpace.exp (-Y)) =
      ContinuousLinearMap.id ℝ A + cmp98AdCLM Y +
        cmp99Eq351ExponentialAdjointRemainderCLM Y := by
  unfold cmp99Eq351ExponentialAdjointRemainderCLM
  abel

/-- Pointwise source form: conjugation is the field itself, the first
commutator, and one internally constructed nonlinear remainder. -/
theorem cmp99Eq351_exponentialAdjoint_apply_eq_linear_add_remainder
    (Y X : A) :
    NormedSpace.exp Y * X * NormedSpace.exp (-Y) =
      X + (Y * X - X * Y) +
        cmp99Eq351ExponentialAdjointRemainderCLM Y X := by
  rw [cmp99Eq351ExponentialAdjointRemainderCLM_apply]
  abel

end

end YangMills.RG
