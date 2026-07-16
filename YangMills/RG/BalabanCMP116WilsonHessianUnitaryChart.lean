import Mathlib
import YangMills.RG.BalabanCMP116WilsonHessianLiteral
import YangMills.RG.SUNAdjointInnerSpace

/-!
# Axiom-free unitary exponential chart for the Wilson mixed variation

Mathlib proves that the exponential of a skew-adjoint matrix is unitary.  It
does not currently provide the determinant identity needed to package the same
matrix directly as an element of `SU(N)`.  This module therefore embeds the
physical `SU(N)` background into `U(N)` and differentiates the same Wilson
trace function along exponentials of genuine `su(N)` matrices.

This is an honest ambient-group extension of the physical action, not an axiom
asserting that the exponential is special unitary.  The future determinant
bridge can strengthen the codomain without changing the curve's underlying
matrix or the scalar action being differentiated.
-/

namespace YangMills.RG

open Matrix

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The ambient unitary group containing the physical special-unitary group. -/
abbrev UN (Nc : ℕ) := Matrix.unitaryGroup (Fin Nc) ℂ

/-- Forget only the determinant-one certificate of a special-unitary matrix. -/
def specialUnitaryToUnitary (U : SUN Nc) : UN Nc :=
  ⟨U.val, (Matrix.mem_specialUnitaryGroup_iff.mp U.property).1⟩

omit [NeZero Nc] in
@[simp]
theorem specialUnitaryToUnitary_coe (U : SUN Nc) :
    (specialUnitaryToUnitary U : Matrix (Fin Nc) (Fin Nc) ℂ) = U.val := rfl

omit [NeZero Nc] in
@[simp]
theorem specialUnitaryToUnitary_one :
    specialUnitaryToUnitary (1 : SUN Nc) = 1 := by
  rfl

omit [NeZero Nc] in
@[simp]
theorem specialUnitaryToUnitary_mul (U V : SUN Nc) :
    specialUnitaryToUnitary (U * V) =
      specialUnitaryToUnitary U * specialUnitaryToUnitary V := by
  rfl

omit [NeZero Nc] in
@[simp]
theorem specialUnitaryToUnitary_inv (U : SUN Nc) :
    specialUnitaryToUnitary U⁻¹ = (specialUnitaryToUnitary U)⁻¹ := by
  rfl

/-- Embed a physical `SU(N)` background into the ambient unitary group without
changing any edge matrix. -/
def physicalBackgroundToUnitary
    (U : PhysicalGaugeBackground d N Nc) : GaugeConfig d N (UN Nc) where
  toFun := fun e => specialUnitaryToUnitary (U e)
  map_reverse := by
    intro e
    rw [← specialUnitaryToUnitary_inv]
    exact congrArg specialUnitaryToUnitary (U.map_reverse e)

omit [NeZero Nc] in
@[simp]
theorem physicalBackgroundToUnitary_apply
    (U : PhysicalGaugeBackground d N Nc) (e : ConcreteEdge d N) :
    physicalBackgroundToUnitary U e = specialUnitaryToUnitary (U e) := rfl

/-- Matrix-valued physical tangent data, one genuine `su(N)` element per
positive physical bond. -/
abbrev PhysicalSuMatrixTangent (d N Nc : ℕ) [NeZero N] :=
  PhysicalBond d N → SuLie Nc

/-- The matrix topology used by the noncommutative Banach-algebra
exponential.  Mathlib provides this construction, but does not register it as
a global instance for square matrices. -/
@[implicit_reducible]
noncomputable def physicalMatrixTopologicalRing (Nc : ℕ) :
    IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
  @Matrix.topologicalRing (Fin Nc) ℂ _ _ _ _


/-- Matrix exponential with Mathlib's explicit square-matrix topological-ring
structure. -/
def physicalMatrixExp (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  @NormedSpace.exp _ _ _ (physicalMatrixTopologicalRing Nc) A

omit [NeZero Nc] in
theorem physicalMatrixExp_conjTranspose
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    (physicalMatrixExp A)ᴴ = physicalMatrixExp Aᴴ := by
  simp only [physicalMatrixExp]
  exact (Matrix.exp_conjTranspose A).symm

omit [NeZero Nc] in
theorem physicalMatrixExp_add_of_commute
    (A B : Matrix (Fin Nc) (Fin Nc) ℂ) (h : Commute A B) :
    physicalMatrixExp (A + B) = physicalMatrixExp A * physicalMatrixExp B := by
  simp only [physicalMatrixExp]
  exact Matrix.exp_add_of_commute A B h

omit [NeZero Nc] in
@[simp]
theorem physicalMatrixExp_zero :
    physicalMatrixExp (0 : Matrix (Fin Nc) (Fin Nc) ℂ) = 1 := by
  simp only [physicalMatrixExp]
  exact @NormedSpace.exp_zero _ _ _ (physicalMatrixTopologicalRing Nc)

/-- The matrix `t X + s Y` is skew-adjoint whenever `X,Y ∈ su(N)`. -/
theorem physicalSuMatrixTangent_skew
    (X Y : PhysicalSuMatrixTangent d N Nc)
    (b : PhysicalBond d N) (t s : ℝ) :
    t • (X b).toMatrix + s • (Y b).toMatrix ∈
      skewAdjoint (Matrix (Fin Nc) (Fin Nc) ℂ) := by
  rw [skewAdjoint.mem_iff]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]
  simp only [star_trivial]
  rw [(mem_suMatrixSubmodule_iff (X b).toMatrix).mp (X b).property |>.1,
    (mem_suMatrixSubmodule_iff (Y b).toMatrix).mp (Y b).property |>.1]
  module

/-- The exponential of the physical skew-adjoint two-parameter generator is
unitary, with no determinant claim. -/
theorem physicalMatrixExp_mem_unitaryGroup
    (X Y : PhysicalSuMatrixTangent d N Nc)
    (b : PhysicalBond d N) (t s : ℝ) :
    physicalMatrixExp (t • (X b).toMatrix + s • (Y b).toMatrix) ∈
      Matrix.unitaryGroup (Fin Nc) ℂ := by
  let Z := t • (X b).toMatrix + s • (Y b).toMatrix
  have hskewStar : star Z = -Z :=
    (skewAdjoint.mem_iff.mp (physicalSuMatrixTangent_skew X Y b t s))
  have hskew : Zᴴ = -Z := by
    simpa [Matrix.star_eq_conjTranspose] using hskewStar
  rw [Matrix.mem_unitaryGroup_iff]
  change physicalMatrixExp Z * (physicalMatrixExp Z)ᴴ = 1
  rw [physicalMatrixExp_conjTranspose, hskew,
    ← physicalMatrixExp_add_of_commute Z (-Z)]
  · simp
  · exact (Commute.refl Z).neg_right

/-- Axiom-free exponential increment in the ambient unitary group. -/
def physicalSuUnitaryIncrement
    (X Y : PhysicalSuMatrixTangent d N Nc)
    (b : PhysicalBond d N) (t s : ℝ) : UN Nc := by
  exact
    ⟨physicalMatrixExp (t • (X b).toMatrix + s • (Y b).toMatrix),
      physicalMatrixExp_mem_unitaryGroup X Y b t s⟩

@[simp]
theorem physicalSuUnitaryIncrement_zero_zero
    (X Y : PhysicalSuMatrixTangent d N Nc) (b : PhysicalBond d N) :
    physicalSuUnitaryIncrement X Y b 0 0 = 1 := by
  apply Subtype.ext
  change physicalMatrixExp
      ((0 : ℝ) • (X b).toMatrix + (0 : ℝ) • (Y b).toMatrix) = 1
  have hz :
      (0 : ℝ) • (X b).toMatrix + (0 : ℝ) • (Y b).toMatrix = 0 := by
    module
  rw [hz, physicalMatrixExp_zero]

/-- The concrete two-parameter CMP99 left variation, represented in the
ambient unitary group but driven by traceless skew-Hermitian directions. -/
def physicalSuUnitaryLeftVariation
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc)
    (t s : ℝ) : GaugeConfig d N (UN Nc) :=
  physicalLeftVariation (physicalBackgroundToUnitary U)
    (physicalSuUnitaryIncrement X Y) t s

@[simp]
theorem physicalSuUnitaryLeftVariation_zero_zero
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc) :
    physicalSuUnitaryLeftVariation U X Y 0 0 =
      physicalBackgroundToUnitary U := by
  exact physicalLeftVariation_zero_zero _ _
    (physicalSuUnitaryIncrement_zero_zero X Y)

/-- Wilson plaquette energy on the ambient unitary extension.  On the embedded
`SU(N)` subgroup it is literally the repository's real-trace observable. -/
def unitaryWilsonPlaquetteEnergy (U : UN Nc) : ℝ :=
  (Matrix.trace U.val).re

/-- Fully concrete, axiom-free mixed derivative of the finite Wilson action
along `su(N)` exponential directions, evaluated through its unitary extension. -/
def physicalWilsonMixedVariationUnitary
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc) : ℝ :=
  wilsonActionMixedVariation unitaryWilsonPlaquetteEnergy
    (physicalBackgroundToUnitary U) (physicalSuUnitaryIncrement X Y)

/-- Concrete plaquette contribution to the same mixed variation. -/
def physicalPlaquetteWilsonMixedVariationUnitary
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) : ℝ :=
  plaquetteWilsonMixedVariation unitaryWilsonPlaquetteEnergy
    (physicalBackgroundToUnitary U) (physicalSuUnitaryIncrement X Y) p

end

end YangMills.RG
