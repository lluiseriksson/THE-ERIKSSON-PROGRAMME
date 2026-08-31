import YangMills.RG.BalabanCMP89CanonicalNeumannReflectionRepresentation
import YangMills.RG.BalabanCMP89SourceNeumannFiniteDepthPhysicalPoincare

/-!
# Flat generated finite-depth canonical CMP89 (2.42) gate

PRE-VALIDATION: source present; `.olean` not yet materialized in a fresh
checkout, and the result has not yet been verified by the compiler.

This module removes the free retained tower and free Poincare certificate from
the canonical Neumann reflection gate at the literal flat background. The
half-open rectangle equivalence, full-space Green action, and exact reflection
identity remain visible source dictionaries; this file does not assert CMP89
(2.42).
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Canonical regional Green at the last positive prefix of the generated
flat finite-depth physical tower. Its radius chain, small-field proof and
Poincare certificate are all constructed internally. -/
noncomputable def cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N)
    (steps : ℕ) {spacing : ℝ} (hspacing : 0 < spacing)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      d M spacing 0 0 steps)
    (mass a : ℝ) (ha : 0 < a) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
        (SUNLieCoord Nc) := by
  let background := cmp99SourceFlatGaugeConfig d
    (cmp99RegionalLatticeSize M N (steps + 1)) Nc
  let chain := cmp99SourceFlatZeroRadiusChain
    (d := d) (M := M) (Nc := Nc) (steps + 1)
  have fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (steps + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0 := by
    intro e
    change ‖((1 : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ 0
    simp
  let T := cmp99SourceGeneratedRetainedPhysicalTower hd hM
    (matrixSUNAdjointModel Nc) Omega (steps + 1) spacing 0
    background chain fineSmall
  let r := cmp85LastPositivePrefix (steps + 1) (Nat.succ_pos steps)
  let CP := cmp89SourceNeumannRecursivePoincareCoefficient
    (cmp89SourceNeumannPhysicalOneScaleCoefficientAt d M spacing)
    (cmp89SourceNeumannPhysicalDerivativeCoefficientAt d M)
    (cmp89SourceNeumannPhysicalFeedbackCoefficientAt d M spacing 0)
    0 steps
  have hCP : 0 < CP :=
    cmp89SourceNeumannRecursivePoincareCoefficient_pos budget
  have hP : CMP89SourceRetainedNeumannPrefixPoincare T r CP := by
    simpa [T, r, CP, CMP89SourceRetainedNeumannPrefixPoincare] using
      (cmp89SourceNeumann_generatedRetainedFiniteDepthPhysicalPoincare
        hd hM Omega steps hspacing background chain fineSmall budget)
  exact cmp89SourceRetainedNeumannPrefixGreen
    T r mass ha hspacing hCP hP

/-- Canonical CMP89 (2.42) proposition at the last positive prefix of one
internally generated flat physical tower. The single recursive contraction
budget constructs the terminal Poincare certificate. The proposition still
requires the literal source dictionaries and reflection equality itself. -/
noncomputable def
    CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannReflectionRepresentation
    {m : Fin d → ℤ}
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N)
    (steps : ℕ) {spacing : ℝ} (hspacing : 0 < spacing)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      d M spacing 0 0 steps)
    (mass a : ℝ) (ha : 0 < a)
    (siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃
      ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1)))
    (fullGreenAction :
      (Fin d → ℤ) → (Fin d → ℤ) → SUNLieCoord Nc → SUNLieCoord Nc) :
    Prop :=
  CMP89CanonicalNeumannReflectionRepresentation siteEquiv
    (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen
      hd hM Omega steps hspacing budget mass a ha)
    fullGreenAction

/-- Projection of the generated flat finite-depth gate. Both remaining
source dictionaries and the physical canonical Green are printed. -/
theorem
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannReflectionRepresentation_eq_series
    {m : Fin d → ℤ}
    {hd : 2 ≤ d} {hM : 2 ≤ M}
    {Omega : ActiveGaugeRegion d N}
    {steps : ℕ} {spacing : ℝ} {hspacing : 0 < spacing}
    {budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      d M spacing 0 0 steps}
    {mass a : ℝ} {ha : 0 < a}
    {siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃
      ActiveGaugeRegion.Site
        (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))}
    {fullGreenAction :
      (Fin d → ℤ) → (Fin d → ℤ) → SUNLieCoord Nc → SUNLieCoord Nc}
    (C : CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannReflectionRepresentation
      hd hM Omega steps hspacing budget mass a ha siteEquiv fullGreenAction)
    (v : SUNLieCoord Nc)
    (x n : CMP89SourceNeumannIntegerRectanglePoint m) :
    cmp89FinitePiLpGreenEntryAt
        (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen
          hd hM Omega steps hspacing budget mass a ha)
        (siteEquiv x) (siteEquiv n) v =
      cmp89NeumannReflectionSeries
        (fun y z ↦ fullGreenAction y z v) m x.1 n.1 :=
  cmp89CanonicalNeumannReflectionRepresentation_eq_series C v x n

end

end YangMills.RG
