import YangMills.RG.BalabanCMP89NeumannRectangleLift
import YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannReflectionRepresentation

/-!
# Compiler-verified canonical generated CMP89 gate on the literal Neumann rectangle

Cold-sealed at source checkpoint `cdd859ba99671e83a1ef2b3d8119a4e376a97ced`;
see Verification Ledger Addendum 1003.

This module removes the free source-site equivalence from the already sealed
generated reflection gate by constructing the terminal complete-block
rectangle internally. It does not assert the physical multiple-reflection
identity or choose a full-space Green action.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {M N Nc : ℕ}
variable [NeZero M] [NeZero N] [NeZero Nc]

/-- Generated finite-depth CMP89 (2.42) gate on the literal half-open source
rectangle. The terminal site equivalence is constructed internally from the
exact complete-block lift. The full-space Green action and the reflection
identity remain visible. -/
noncomputable def
    CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation
    {m : Fin 4 → ℤ}
    (hM : 2 ≤ M) (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (steps : ℕ) {spacing : ℝ} (hspacing : 0 < spacing)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      4 M spacing 0 0 steps)
    (mass a : ℝ) (ha : 0 < a)
    (fullGreenAction :
      (Fin 4 → ℤ) → (Fin 4 → ℤ) → SUNLieCoord Nc → SUNLieCoord Nc) :
    Prop :=
  CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannReflectionRepresentation
    (d := 4) (M := M) (N := N) (Nc := Nc)
    (m := cmp89SourceNeumannScaleRectangleSidePow M (steps + 1) m)
    (by norm_num) hM
    (cmp89SourceNeumannRectangleActiveRegion (N := N) m)
    steps hspacing budget mass a ha
    (cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv
      (M := M) (N := N) hm hfit (steps + 1))
    fullGreenAction

/-- Projection of the rectangle-specialized gate. The regional entry is the
canonical generated inverse, and the only remaining input to the equality is
the literal full-space action. -/
theorem
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation_eq_series
    {m : Fin 4 → ℤ}
    {hM : 2 ≤ M} {hm : ∀ mu, 0 < m mu}
    {hfit : ∀ mu, m mu ≤ (N : ℤ)}
    {steps : ℕ} {spacing : ℝ} {hspacing : 0 < spacing}
    {budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      4 M spacing 0 0 steps}
    {mass a : ℝ} {ha : 0 < a}
    {fullGreenAction :
      (Fin 4 → ℤ) → (Fin 4 → ℤ) → SUNLieCoord Nc → SUNLieCoord Nc}
    (C :
      CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation
        hM hm hfit steps hspacing budget mass a ha fullGreenAction)
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
        (fun y z ↦ fullGreenAction y z v)
        (cmp89SourceNeumannScaleRectangleSidePow M (steps + 1) m)
        x.1 n.1 := by
  exact
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannReflectionRepresentation_eq_series
      (d := 4) (M := M) (N := N) (Nc := Nc)
      (m := cmp89SourceNeumannScaleRectangleSidePow M (steps + 1) m)
      (hd := by norm_num) (hM := hM)
      (Omega := cmp89SourceNeumannRectangleActiveRegion (N := N) m)
      (steps := steps) (hspacing := hspacing) (budget := budget)
      (mass := mass) (a := a) (ha := ha)
      (siteEquiv := cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv
        (M := M) (N := N) hm hfit (steps + 1))
      (fullGreenAction := fullGreenAction) C v x n

end

end YangMills.RG
