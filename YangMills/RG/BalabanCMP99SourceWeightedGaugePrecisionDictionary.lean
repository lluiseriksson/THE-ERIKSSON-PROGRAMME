import YangMills.RG.BalabanCMP99SourceGaugePrecision
import YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime
import YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# Counting/weighted coefficient dictionary for the CMP99 precision

The source-weighted tower stores the printed adjoint explicitly, whereas the
repository's finite-dimensional real precision is presented using Lean's
counting-space Hilbert adjoint.  This file exposes the exact volume-element
ratio between those presentations before any real/complex specialization is
attempted.  Omitting the ratio would silently change the coefficient of the
`Q'^* Q'` term while preserving every operator type.
-/

namespace YangMills.RG

noncomputable section

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

variable {d N : ℕ} {g : Type} [NeZero N]
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]
variable {Omega : ActiveGaugeRegion d N} {spacing : ℝ}

/-- Printed source-weighted-adjoint coefficient induced by a coefficient on
Lean's counting-space Hilbert adjoint. -/
def cmp99SourceCountingCoefficientAsWeightedAdjoint
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (a : ℝ) : ℝ :=
  a * (spacing ^ d / T.terminalSpacing ^ d)

/-- Exact presentation of the counting-Hilbert precision through the printed
source-weighted adjoint.  The spacing ratio is derived from the tower and is
not a caller-supplied normalization equality. -/
theorem cmp99SourceGaugePrecision_eq_weightedAdjoint
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (Delta : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    (a : ℝ) (hterminal : T.terminalSpacing ≠ 0) :
    cmp99SourceGaugePrecision Delta T.Qprime a =
      Delta + cmp99SourceCountingCoefficientAsWeightedAdjoint T a •
        (T.weightedAdjoint.comp T.Qprime) := by
  rw [cmp99SourceGaugePrecision,
    T.adjoint_eq_spacingRatio_smul_weightedAdjoint hterminal]
  apply ContinuousLinearMap.ext
  intro phi
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,
    cmp99SourceCountingCoefficientAsWeightedAdjoint]
  module

/-- On the literal source-generated tower the counting coefficient contains
exactly the terminal-scale ratio `spacing^d / (M^depth * spacing)^d`.  The
terminal spacing is derived from the generated tower; it is not supplied as a
free dictionary equality. -/
theorem CMP99SourceActiveRegionChain.weightedQprimeTower_countingCoefficient_asWeightedAdjoint
    {M Nc depth : ℕ} [NeZero d] [NeZero M] [NeZero Nc]
    {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (hd : 2 ≤ d) (hM : 2 ≤ M) (rho : SUNAdjointModel Nc)
    (spacing epsilon a : ℝ) (background : GaugeConfig d N (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d N,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    letI : NeZero N := regions.neZero
    cmp99SourceCountingCoefficientAsWeightedAdjoint
        (regions.weightedQprimeTower hd hM rho spacing epsilon background
          chain fineSmall) a =
      a * (spacing ^ d / (((M : ℝ) ^ depth * spacing) ^ d)) := by
  letI : NeZero N := regions.neZero
  have hterminal :
      (regions.weightedQprimeTower hd hM rho spacing epsilon background chain
        fineSmall).terminalSpacing = (M : ℝ) ^ depth * spacing :=
    regions.weightedQprimeTower_terminalSpacing hd hM rho spacing epsilon
      background chain fineSmall
  unfold cmp99SourceCountingCoefficientAsWeightedAdjoint
  rw [hterminal]

end

end YangMills.RG
