import YangMills.RG.BalabanCMP99SourceGaugePrecision
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

variable {d N : ℕ} {g : Type} [NeZero N]
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]
variable {Omega : ActiveGaugeRegion d N} {spacing : ℝ}

/-- Counting-Hilbert coefficient corresponding to a printed coefficient on
the source-weighted adjoint. -/
def cmp99SourceWeightedAdjointCountingCoefficient
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
      Delta + cmp99SourceWeightedAdjointCountingCoefficient T a •
        (T.weightedAdjoint.comp T.Qprime) := by
  rw [cmp99SourceGaugePrecision,
    T.adjoint_eq_spacingRatio_smul_weightedAdjoint hterminal]
  apply ContinuousLinearMap.ext
  intro phi
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,
    cmp99SourceWeightedAdjointCountingCoefficient]
  module

end

end YangMills.RG
