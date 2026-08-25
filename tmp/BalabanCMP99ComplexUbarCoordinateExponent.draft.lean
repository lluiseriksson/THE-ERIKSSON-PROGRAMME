import YangMills.RG.BalabanCMP99ComplexUbarSpecialLinear
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedBackground

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# The literal analytic Ubar exponent in physical complex coordinates

The complex Ubar algebra already constructs the exponent as the normalized
sum of the principal Mercator logarithms of literal determinant-one path
deviations.  This module does not accept a coordinate exponent as caller
data.  It packages that same matrix in Mathlib's `sl(N,C)` carrier and pulls
it back through the explicit physical complex-coordinate equivalence.

The terminal equality says that mapping this internally generated coordinate
back to matrices recovers the literal logarithmic sum exactly.  This is the
typed algebraic dictionary needed before the source recursion (160)--(162)
can be represented by a scale-indexed coordinate `Q_j` without postulating a
free family.  No Proposition-4 norm estimate or recursive background chain is
claimed here.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- The literal determinant-one Ubar exponent in Mathlib's trace-zero
carrier.  Tracelessness is derived from the same local near-identity and
no-winding hypotheses that construct the analytic factor. -/
noncomputable def cmp99UbarSpecialLinearExponentSl {ι : Type*}
    (s : Finset ι) (w : ι → ℝ)
    (D : ι → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi) :
    LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ :=
  ⟨cmp99UbarSpecialLinearExponent s w D,
    trace_cmp99UbarSpecialLinearExponent_eq_zero
      s w D hD hnoWinding⟩

@[simp] theorem cmp99UbarSpecialLinearExponentSl_val {ι : Type*}
    (s : Finset ι) (w : ι → ℝ)
    (D : ι → Matrix.SpecialLinearGroup (Fin Nc) ℂ) (hD) (hnoWinding) :
    (cmp99UbarSpecialLinearExponentSl s w D hD hnoWinding).1 =
      cmp99UbarSpecialLinearExponent s w D :=
  rfl

/-- The source-generated complex Lie coordinate of the literal analytic Ubar
exponent.  It is the inverse image of the constructed trace-zero matrix, not
a coordinate selected by the caller. -/
noncomputable def cmp99UbarSpecialLinearExponentCoord {ι : Type*}
    (s : Finset ι) (w : ι → ℝ)
    (D : ι → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi) : SUNLieComplexCoord Nc :=
  (cmp99SUNLieComplexCoordSlEquiv Nc).symm
    (cmp99UbarSpecialLinearExponentSl s w D hD hnoWinding)

/-- Returning the internally generated coordinate to matrices gives exactly
the printed logarithmic exponent.  This is the non-vacuous `Q_j` dictionary:
the right-hand side is built from the literal deviations and no independent
coordinate or equality is an input. -/
@[simp] theorem cmp99SUNLieComplexCoordMatrixLM_exponentCoord {ι : Type*}
    (s : Finset ι) (w : ι → ℝ)
    (D : ι → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi) :
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99UbarSpecialLinearExponentCoord s w D hD hnoWinding) =
      cmp99UbarSpecialLinearExponent s w D := by
  have h := (cmp99SUNLieComplexCoordSlEquiv Nc).apply_symm_apply
    (cmp99UbarSpecialLinearExponentSl s w D hD hnoWinding)
  exact congrArg
    (fun Z : LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ => Z.1) h

/-- Consequently the existing determinant-one analytic factor is literally
the matrix exponential of the internally generated physical complex
coordinate. -/
theorem cmp99UbarSpecialLinearFactorOfNearIdentity_coe_eq_exp_coord
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (D : ι → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (hD : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ i ∈ s, (Nc : ℝ) *
      ‖nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ <
        2 * Real.pi) :
    (cmp99UbarSpecialLinearFactorOfNearIdentity
        s w D hD hnoWinding : Matrix (Fin Nc) (Fin Nc) ℂ) =
      NormedSpace.exp
        (cmp99SUNLieComplexCoordMatrixLM Nc
          (cmp99UbarSpecialLinearExponentCoord s w D hD hnoWinding)) := by
  rw [cmp99UbarSpecialLinearFactorOfNearIdentity_coe,
    cmp99SUNLieComplexCoordMatrixLM_exponentCoord]

end

end YangMills.RG
