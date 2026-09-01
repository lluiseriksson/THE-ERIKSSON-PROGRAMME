import YangMills.RG.BalabanCMP89CanonicalNeumannReflectionInverseProducer
import YangMills.RG.BalabanCMP89NeumannPhysicalRealReflectionSummability
import YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision

/-!
# PRE-VALIDATION: source-faithful physical CMP89 Neumann reflection producer

The source is present, but its `.olean` has not yet been materialized and the
result has not yet been verified by the compiler.

This draft fixes the two scalar dictionaries that the earlier physical
proposition left implicit.  The retained regional precision is built at the
canonical generated spacing from the source coefficient `aSource`, whereas
the literal CMP89 (2.48) Fourier Green uses the corresponding weighted
coefficient.  The only remaining analytic equality is the right-inverse law
for the internally constructed reflection operator.

This file is not imported by `YangMillsCore` before its cold gate passes.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {M N Nc : ℕ}
variable [NeZero M] [NeZero N] [NeZero Nc]

/-- Canonical fine spacing for the terminal prefix used by CMP89 (2.48). -/
noncomputable def
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing
    (M steps : ℕ) : ℝ :=
  cmp99SourceGeneratedFullComplexSpacing M (steps + 1)

/-- Source-faithful Fourier coefficient: the source parameter is transported
to the weighted-adjoint convention of the literal full-lattice precision. -/
noncomputable def
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannFourierCoefficient
    (hM : 2 ≤ M) (Omega : ActiveGaugeRegion 4 N)
    (steps : ℕ) (aSource : ℝ) : ℝ :=
  let spacing :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing M steps
  let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
    (Nc := Nc) (by norm_num) hM Omega steps spacing
  let r :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
  cmp85SourcePrefixWeightedCoefficient T aSource r

/-- At canonical fine spacing, the terminal retained spacing is exactly one.
This is the scalar normalization that prevents a second block-volume factor
from being inserted into the Fourier coefficient. -/
theorem
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTerminalSpacing_eq_one
    (hM : 2 ≤ M) (Omega : ActiveGaugeRegion 4 N) (steps : ℕ) :
    ((cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
        (Nc := Nc) (by norm_num) hM Omega steps
        (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing
          M steps)).towerAt
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps).1).
        terminalSpacing = 1 := by
  let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
    (Nc := Nc) (by norm_num) hM Omega steps
    (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing
      M steps)
  change
    (T.towerAt
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps).1).
        terminalSpacing = 1
  have hM0 : (M : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hpow : (M : ℝ) ^ (steps + 1) ≠ 0 :=
    pow_ne_zero _ hM0
  rw [T.towerAt_terminalSpacing]
  simp [cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix,
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing,
    cmp99SourceGeneratedFullComplexSpacing,
    cmp99SourceGeneratedFullComplexBlockSide, Nat.cast_pow,
    hpow]

/-- Closed printed coefficient at the terminal canonical scale.  The
Fourier coefficient is `a_j`; no counting-volume factor survives here. -/
theorem
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannFourierCoefficient_eq_prefixA
    (hM : 2 ≤ M) (Omega : ActiveGaugeRegion 4 N)
    (steps : ℕ) (aSource : ℝ) :
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannFourierCoefficient
        (Nc := Nc) hM Omega steps aSource =
      cmp85SourcePrefixA (M := M) aSource
        (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps) := by
  unfold cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannFourierCoefficient
  unfold cmp85SourcePrefixWeightedCoefficient
  rw [cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTerminalSpacing_eq_one]
  norm_num

/-- Literal real scalar kernel used by the source-faithful image operator. -/
def cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalFullGreen
    (hM : 2 ≤ M) (Omega : ActiveGaugeRegion 4 N)
    (steps : ℕ) (mass aSource : ℝ)
    (x y : Fin 4 → ℤ) : ℝ :=
  (cmp89Eq248PhysicalFullLatticeGreen M (steps + 1) mass
    (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannFourierCoefficient
      (Nc := Nc) hM Omega steps aSource) x y).re

/-- Exact right-inverse equation left by the physical CMP89 (2.42) producer.
All geometry, spacing and coefficient conventions are fixed in the type. -/
def CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalRightInverse
    {m : Fin 4 → ℤ}
    (hM : 2 ≤ M) (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (steps : ℕ)
    (mass aSource : ℝ) : Prop :=
  let Omega := cmp89SourceNeumannRectangleActiveRegion (N := N) m
  let spacing :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing M steps
  let precision :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
      (Nc := Nc) (by norm_num) hM Omega steps spacing mass aSource
  let siteEquiv := cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv
    (M := M) (N := N) hm hfit (steps + 1)
  let fullGreen :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalFullGreen
      (Nc := Nc) hM Omega steps mass aSource
  precision.comp
      (cmp89NeumannScalarReflectionOperator
        (g := SUNLieCoord Nc) siteEquiv fullGreen) =
    ContinuousLinearMap.id ℝ
      (ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
        (SUNLieCoord Nc))

/-- Conditional source-faithful CMP89 (2.42) producer.  The target
representation is derived by inverse uniqueness; it is not accepted as an
input. -/
theorem
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalRepresentation_of_rightInverse
    {m : Fin 4 → ℤ}
    (hM : 2 ≤ M) (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu ≤ (N : ℤ))
    (steps : ℕ)
    (budget : CMP89SourceNeumannPhysicalRecursiveContractionBudget
      4 M
        (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing
          M steps)
        0 0 steps)
    (mass : ℝ) {aSource rho : ℝ} (haSource : 0 < aSource)
    (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannFourierCoefficient
        (Nc := Nc) hM
          (cmp89SourceNeumannRectangleActiveRegion (N := N) m)
          steps aSource)
      rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (himage :
      CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalRightInverse
        (Nc := Nc) hM hm hfit steps mass aSource) :
    CMP89CanonicalNeumannReflectionRepresentation
      (d := 4) (N := cmp99RegionalLatticeSize M N (steps + 1))
      (g := SUNLieCoord Nc)
      (Omega := cmp99IteratedLiftActiveRegion (M := M)
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m) (steps + 1))
      (m := cmp89SourceNeumannScaleRectangleSidePow M (steps + 1) m)
      (cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv
        (M := M) (N := N) hm hfit (steps + 1))
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen
        (d := 4) (M := M) (N := N) (Nc := Nc)
        (by norm_num) hM
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m)
        steps
        (cmp99SourceGeneratedFullComplexSpacing_pos M (steps + 1))
        budget mass aSource haSource)
      (fun x y v =>
        cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalFullGreen
          (Nc := Nc) hM
            (cmp89SourceNeumannRectangleActiveRegion (N := N) m)
            steps mass aSource x y • v) := by
  let Omega := cmp89SourceNeumannRectangleActiveRegion (N := N) m
  let spacing :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing M steps
  let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
    (Nc := Nc) (by norm_num) hM Omega steps spacing
  let r :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
  let CP :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient
      4 M spacing steps
  let aFourier := cmp85SourcePrefixWeightedCoefficient T aSource r
  let c := min 1 (cmp85SourcePrefixCountingCoefficient T aSource r / CP)
  let precision :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
      (Nc := Nc) (by norm_num) hM Omega steps spacing mass aSource
  let green :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannGreen
      (d := 4) (M := M) (N := N) (Nc := Nc)
      (by norm_num) hM Omega steps
      (cmp99SourceGeneratedFullComplexSpacing_pos M (steps + 1))
      budget mass aSource haSource
  let siteEquiv := cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv
    (M := M) (N := N) hm hfit (steps + 1)
  let fullGreen :=
    cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalFullGreen
      (Nc := Nc) hM Omega steps mass aSource
  have hspacing : 0 < spacing := by
    simpa [spacing,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing] using
      (cmp99SourceGeneratedFullComplexSpacing_pos M (steps + 1))
  have hCP : 0 < CP := by
    simpa [CP,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPoincareCoefficient]
      using cmp89SourceNeumannRecursivePoincareCoefficient_pos budget
  have hcount :
      0 < cmp85SourcePrefixCountingCoefficient T aSource r :=
    cmp85SourcePrefixCountingCoefficient_pos T haSource hspacing r
  have hc : 0 < c := by
    exact lt_min (by norm_num) (div_pos hcount hCP)
  have hcoercive : IsCoerciveCLM precision c := by
    simpa [precision, c, T, r, CP, Omega, spacing] using
      (isCoerciveCLM_cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision
        (Nc := Nc) (by norm_num) hM Omega steps hspacing budget mass haSource)
  have hgreen : precision.comp green =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain
          (cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
          (SUNLieCoord Nc)) := by
    simpa [precision, green, Omega, spacing] using
      (cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision_comp_green
        (Nc := Nc) (by norm_num) hM Omega steps hspacing budget mass haSource)
  have haFourier : 0 ≤ aFourier := by
    exact (cmp85SourcePrefixWeightedCoefficient_pos
      T haSource hspacing r).le
  have hside : ∀ mu,
      0 < cmp89SourceNeumannScaleRectangleSidePow M (steps + 1) m mu := by
    intro mu
    dsimp [cmp89SourceNeumannScaleRectangleSidePow]
    exact mul_pos
      (by exact_mod_cast
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne M)) (steps + 1)))
      (hm mu)
  have hsummable : ∀ x n : CMP89SourceNeumannIntegerRectanglePoint
      (cmp89SourceNeumannScaleRectangleSidePow M (steps + 1) m),
      Summable (fun k : Fin 4 → ℤ =>
        ∑ branch : CMP89NeumannReflectionBranch 4,
          fullGreen x.1
            (cmp89NeumannReflectionImage
              (cmp89SourceNeumannScaleRectangleSidePow M (steps + 1) m)
              n.1 k branch)) := by
    intro x n
    simpa [fullGreen,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalFullGreen,
      aFourier, T, r, Omega, spacing,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannFourierCoefficient,
      cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing] using
      (summable_cmp89Eq248PhysicalRealNeumannReflection_sum
        (L := M) (j := steps + 1) (mass := mass) (a := aFourier)
        (rho := rho) haFourier hrho hamplitude
        hradius
        (by simpa [aFourier, T, r, Omega, spacing,
          cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannFourierCoefficient,
          cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing]
          using hwindow)
        hmass hside)
  apply cmp89CanonicalNeumannReflectionRepresentation_of_rightInverse
    (d := 4) (N := cmp99RegionalLatticeSize M N (steps + 1))
    (g := SUNLieCoord Nc)
    (Omega := cmp99IteratedLiftActiveRegion (M := M) Omega (steps + 1))
    (m := cmp89SourceNeumannScaleRectangleSidePow M (steps + 1) m)
    siteEquiv precision green fullGreen hc hcoercive hgreen
  · simpa [CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalRightInverse,
      Omega, spacing, precision, siteEquiv, fullGreen] using himage
  · exact hside
  · exact hsummable

end

end YangMills.RG
