import YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannReflectionRepresentation

/-!
# PRE-VALIDATION: generated flat finite-depth canonical Neumann precision

The source is present, but its `.olean` has not yet been materialized and the
result has not yet been verified by the compiler.

This module exposes the exact precision paired with
`cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen`.  The flat
background, zero-radius chain, retained tower, last positive prefix and
recursive Poincare coefficient are all constructed internally.  The public
endpoint records coercivity and both inverse laws for that one literal pair.

It does not prove the reflected full-lattice right-inverse identity CMP89
(2.42), a Green-kernel bound, or window 15.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The retained physical tower used by the generated finite-depth canonical
Neumann Green.  Naming it makes the precision/Green agreement visible rather
than leaving it inside two independent tactic blocks. -/
noncomputable def cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N) (steps : ℕ) (spacing : ℝ) :=
  cmp99SourceGeneratedRetainedPhysicalTower hd hM
    (matrixSUNAdjointModel Nc) Omega (steps + 1) spacing 0
    (cmp99SourceFlatGaugeConfig d
      (cmp99RegionalLatticeSize M N (steps + 1)) Nc)
    (cmp99SourceFlatZeroRadiusChain
      (d := d) (M := M) (Nc := Nc) (steps + 1))
    cmp99SourceFlatGaugeConfig_zero_small

/-- Last positive prefix of the generated tower. -/
def cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix
    (steps : ℕ) : CMP85PositivePrefix (steps + 1) :=
  ⟨Fin.last (steps + 1), Nat.succ_pos steps⟩

/-- Exact recursive Poincare coefficient used by the generated canonical
Neumann Green at radius zero. -/
noncomputable def
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient
    (d M : ℕ) [NeZero d] [NeZero M] (spacing : ℝ) (steps : ℕ) : ℝ :=
  cmp89SourceNeumannRecursivePoincareCoefficient
    (cmp89SourceNeumannPhysicalOneScaleCoefficientAt d M spacing)
    (cmp89SourceNeumannPhysicalDerivativeCoefficientAt d M)
    (cmp89SourceNeumannPhysicalFeedbackCoefficientAt d M spacing 0)
    0 steps

/-- The literal three-term regional precision paired with the generated
finite-depth canonical Neumann Green. -/
noncomputable def cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N) (steps : ℕ)
    (spacing mass a : ℝ) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
        (SUNLieCoord Nc) :=
  cmp89SourceRetainedNeumannPrefixGaugePrecision
    (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
      (Nc := Nc) hd hM Omega steps spacing)
    (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps)
    mass a

/-- The recursive contraction budget constructs the exact retained-prefix
Poincare certificate consumed by the canonical pair. -/
theorem
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincare
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N) (steps : ℕ)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      d M spacing 0 0 steps) :
    CMP89SourceRetainedNeumannPrefixPoincare
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
        (Nc := Nc) hd hM Omega steps spacing)
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps)
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient
        d M spacing steps) := by
  simpa [cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient,
      CMP89SourceRetainedNeumannPrefixPoincare] using
    (cmp89SourceNeumann_generatedRetainedFiniteDepthPhysicalPoincare
      (Nc := Nc) hd hM Omega steps hspacing
      (cmp99SourceFlatGaugeConfig d
        (cmp99RegionalLatticeSize M N (steps + 1)) Nc)
      (cmp99SourceFlatZeroRadiusChain
        (d := d) (M := M) (Nc := Nc) (steps + 1))
      cmp99SourceFlatGaugeConfig_zero_small budget)

/-- Coercivity of the exact generated finite-depth canonical Neumann
precision.  The floor remains literal and independent of the bare mass. -/
theorem
    isCoerciveCLM_cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N) (steps : ℕ)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      d M spacing 0 0 steps)
    (mass : ℝ) {a : ℝ} (ha : 0 < a) :
    IsCoerciveCLM
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
        (Nc := Nc) hd hM Omega steps spacing mass a)
      (min 1
          (cmp85SourcePrefixCountingCoefficient
            (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
              (Nc := Nc) hd hM Omega steps spacing)
            a
            (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps)) /
        cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient
          d M spacing steps) := by
  let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
    (Nc := Nc) hd hM Omega steps spacing
  let r := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
  let CP :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient
      d M spacing steps
  have hCP : 0 < CP := by
    simpa [CP,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient]
      using cmp89SourceNeumannRecursivePoincareCoefficient_pos budget
  have hP : CMP89SourceRetainedNeumannPrefixPoincare T r CP := by
    simpa [T, r, CP] using
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincare
        (Nc := Nc) hd hM Omega steps hspacing budget)
  simpa [cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision,
      T, r, CP] using
    (isCoerciveCLM_cmp89SourceRetainedNeumannPrefixGaugePrecision
      T r mass ha hspacing hCP hP)

/-- The generated precision followed by the already sealed canonical Green is
the identity.  This is the exact internal inverse law needed before the
reflected full-lattice operator can be compared to that Green. -/
theorem
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision_comp_green
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N) (steps : ℕ)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      d M spacing 0 0 steps)
    (mass : ℝ) {a : ℝ} (ha : 0 < a) :
    (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
        (Nc := Nc) hd hM Omega steps spacing mass a).comp
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen
        (Nc := Nc) hd hM Omega steps hspacing budget mass a ha) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain
          (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
          (SUNLieCoord Nc)) := by
  let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
    (Nc := Nc) hd hM Omega steps spacing
  let r := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
  let CP :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient
      d M spacing steps
  have hCP : 0 < CP := by
    simpa [CP,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient]
      using cmp89SourceNeumannRecursivePoincareCoefficient_pos budget
  have hP : CMP89SourceRetainedNeumannPrefixPoincare T r CP := by
    simpa [T, r, CP] using
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincare
        (Nc := Nc) hd hM Omega steps hspacing budget)
  simpa [cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient,
      T, r, CP] using
    (cmp89SourceRetainedNeumannPrefixGaugePrecision_comp_green
      T r mass ha hspacing hCP hP)

/-- The same canonical Green is also a left inverse of the generated
precision. -/
theorem
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen_comp_precision
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega : ActiveGaugeRegion d N) (steps : ℕ)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      d M spacing 0 0 steps)
    (mass : ℝ) {a : ℝ} (ha : 0 < a) :
    (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen
        (Nc := Nc) hd hM Omega steps hspacing budget mass a ha).comp
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
        (Nc := Nc) hd hM Omega steps spacing mass a) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain
          (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
          (SUNLieCoord Nc)) := by
  let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
    (Nc := Nc) hd hM Omega steps spacing
  let r := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
  let CP :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient
      d M spacing steps
  have hCP : 0 < CP := by
    simpa [CP,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient]
      using cmp89SourceNeumannRecursivePoincareCoefficient_pos budget
  have hP : CMP89SourceRetainedNeumannPrefixPoincare T r CP := by
    simpa [T, r, CP] using
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincare
        (Nc := Nc) hd hM Omega steps hspacing budget)
  simpa [cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient,
      T, r, CP] using
    (cmp89SourceRetainedNeumannPrefixGreen_comp_gaugePrecision
      T r mass ha hspacing hCP hP)

end

end YangMills.RG
