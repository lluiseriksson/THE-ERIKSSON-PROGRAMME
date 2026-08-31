import YangMills.RG.BalabanCMP89NeumannRectangularPhysicalGreenInsertion
import YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation

/-!
# PRE-VALIDATION: physical full-space action in the canonical CMP89 rectangle gate

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

This module fixes the remaining full-space action to the real slice of the
literal normalized CMP89 (2.48) Fourier Green. It does not assert that the
complex scalar is real and it does not prove the multiple-reflection identity
(2.42): that identity remains the proposition produced by this definition.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {M N Nc : ℕ}
variable [NeZero M] [NeZero N] [NeZero Nc]

/-- Real-fibre action of the literal complex CMP89 (2.48) full-lattice Green.
The real projection is written in the definition rather than hidden in a
scalar-action dictionary. -/
def cmp89Eq248PhysicalFullLatticeGreenRealAction
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (x y : Fin 4 → ℤ) (v : SUNLieCoord Nc) : SUNLieCoord Nc :=
  (cmp89Eq248PhysicalFullLatticeGreen L j mass a x y).re • v

/-- Generated finite-depth canonical CMP89 gate with both the terminal site
equivalence and the full-space Green action constructed internally. Its
content is exactly the still-open reflection identity for the literal real
slice of (2.48). -/
noncomputable def
    CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation
    {m : Fin 4 → ℤ}
    (hM : 2 ≤ M) (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (steps : ℕ) {spacing : ℝ} (hspacing : 0 < spacing)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      4 M spacing 0 0 steps)
    (mass a : ℝ) (ha : 0 < a) : Prop :=
  CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation
    hM hm hfit steps hspacing budget mass a ha
    (cmp89Eq248PhysicalFullLatticeGreenRealAction
      (Nc := Nc) M (steps + 1) mass a)

/-- Projection of the fully specialized gate. No arbitrary site equivalence
or full-space action remains in the statement. -/
theorem
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation_eq_series
    {m : Fin 4 → ℤ}
    {hM : 2 ≤ M} {hm : ∀ mu, 0 < m mu}
    {hfit : ∀ mu, m mu ≤ (N : ℤ)}
    {steps : ℕ} {spacing : ℝ} {hspacing : 0 < spacing}
    {budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      4 M spacing 0 0 steps}
    {mass a : ℝ} {ha : 0 < a}
    (C :
      CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation
        (Nc := Nc) hM hm hfit steps hspacing budget mass a ha)
    (v : SUNLieCoord Nc)
    (x n : CMP89SourceNeumannIntegerRectanglePoint
      (cmp89SourceNeumannScaleRectangleSidePow M (steps + 1) m)) :
    cmp89FinitePiLpGreenEntryAt
        (d := 4) (N := cmp99RegionalLatticeSize M N (steps + 1))
        (g := SUNLieCoord Nc)
        (Omega := cmp99IteratedLiftActiveRegion (M := M)
          (cmp89SourceNeumannRectangleActiveRegion (N := N) m) (steps + 1))
        (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen
          (d := 4) (M := M) (N := N) (Nc := Nc)
          (by norm_num) hM
          (cmp89SourceNeumannRectangleActiveRegion (N := N) m)
          steps hspacing budget mass a ha)
        (cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv
          (M := M) (N := N) hm hfit (steps + 1) x)
        (cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv
          (M := M) (N := N) hm hfit (steps + 1) n)
        v =
      cmp89NeumannReflectionSeries
        (fun y z => cmp89Eq248PhysicalFullLatticeGreenRealAction
          (Nc := Nc) M (steps + 1) mass a y z v)
        (cmp89SourceNeumannScaleRectangleSidePow M (steps + 1) m)
        x.1 n.1 := by
  exact
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation_eq_series
      C v x n

end

end YangMills.RG
