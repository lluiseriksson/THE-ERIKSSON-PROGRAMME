import YangMills.RG.BalabanCMP89SourceNeumannPhysicalOneStepScaling

/-!
# Two-scale physical CMP89 Neumann absorption

The coarse Poincare package is constructed internally from the literal next
active region, its block-saturation certificate, and the next physical
background.  Thus the caller supplies only the fine Neumann-kernel equation
and the vanishing of the literal two-step transported average.  Physical
fine/coarse deviations carry their lattice-spacing factors explicitly, and
the final smallness hypothesis is the dimensionless gate proved in the
one-step scaling dictionary.

This is a two-scale joint-kernel producer.  It is not an arbitrary-depth
uniform Poincare theorem and does not by itself attain window 15.
-/

namespace YangMills.RG

open YangMills
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N'' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N''] [NeZero Nc]

/-- A fine Neumann-kernel field whose literal two consecutive physical
averages vanish is zero whenever the spacing-free one-step budget contracts.
The next-scale Poincare certificate is produced internally. -/
theorem eq_zero_of_cmp89SourceNeumann_twoScale_physical_absorption
    (Omega : ActiveGaugeRegion d (M * (M * N'')))
    (hOmega : Omega.BlockSaturated)
    (hOmegaC :
      (cmp99ActiveCoarseRegion (M := M) (N' := M * N'') Omega).BlockSaturated)
    (U : PhysicalGaugeBackground d (M * (M * N'')) Nc)
    (V : PhysicalGaugeBackground d (M * N'') Nc)
    {spacing : ℝ} (hspacing : 0 < spacing)
    (etaFine etaCoarse : ℝ)
    (etaFine_nonneg : 0 ≤ etaFine)
    (etaCoarse_nonneg : 0 ≤ etaCoarse)
    (hnext : |(M : ℝ) * spacing| ≤ 1)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hD : cmp89SourceNeumannRegionalCovariantD0CLM
      Omega (matrixSUNAdjointModel Nc) U spacing phi = 0)
    (hQ :
      cmp99SourceTransportedBlockAverageCLM
          (cmp99ActiveCoarseRegion (M := M) (N' := M * N'') Omega)
          (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) V)
          (cmp99SourceTransportedBlockAverageCLM Omega
            (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) U)
            phi) = 0)
    (fine_small : ∀ e : ConcreteEdge d (M * (M * N'')),
      ‖(U e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ spacing * etaFine)
    (coarse_small : ∀ b : PhysicalBond d (M * N''),
      ‖(V (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
          ((M : ℝ) * spacing) * etaCoarse)
    (hsmall :
      cmp99OneScaleBlockPoincareConstant d M *
          cmp89SourceNeumannPhysicalOneStepDefectCoefficient
            d M etaFine etaCoarse < 1) :
    phi = 0 := by
  let OmegaC :=
    cmp99ActiveCoarseRegion (M := M) (N' := M * N'') Omega
  let Qnext := cmp99SourceTransportedBlockAverageCLM OmegaC
    (cmp99SourceWeightedPhysicalTransport (matrixSUNAdjointModel Nc) V)
  have hspacing0 : spacing ≠ 0 := ne_of_gt hspacing
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hcoarseSpacing : (M : ℝ) * spacing ≠ 0 :=
    mul_ne_zero hM hspacing0
  have hP : CMP89SourceNeumannRegionalPoincare
      OmegaC (matrixSUNAdjointModel Nc) V Qnext ((M : ℝ) * spacing)
        (cmp89SourceNeumannOneScalePoincareConstant
          d M ((M : ℝ) * spacing)) := by
    exact cmp89SourceNeumann_oneScale_quantitativePoincare
      OmegaC hOmegaC (matrixSUNAdjointModel Nc) V hcoarseSpacing
  have hCP : 0 < cmp89SourceNeumannOneScalePoincareConstant
      d M ((M : ℝ) * spacing) :=
    cmp89SourceNeumannOneScalePoincareConstant_pos
      ((M : ℝ) * spacing)
  have hfineNonneg : 0 ≤ spacing * etaFine :=
    mul_nonneg hspacing.le etaFine_nonneg
  have hcoarseNonneg : 0 ≤ ((M : ℝ) * spacing) * etaCoarse := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg M) hspacing.le)
      etaCoarse_nonneg
  have hsmall' :
      cmp89SourceNeumannOneScalePoincareConstant
          d M ((M : ℝ) * spacing) *
        cmp89SourceNeumannOneStepDefectCoefficient
          (d := d) (M := M) spacing (spacing * etaFine)
            (((M : ℝ) * spacing) * etaCoarse) < 1 :=
    (cmp89SourceNeumannOneScalePoincare_mul_defect_lt_one_iff
      (d := d) (M := M) hspacing0 hnext etaFine etaCoarse).2 hsmall
  exact eq_zero_of_cmp89SourceNeumann_oneStep_absorption
    Omega hOmega U V Qnext hspacing0
    (cmp89SourceNeumannOneScalePoincareConstant
      d M ((M : ℝ) * spacing)) hCP hP phi hD hQ
    (spacing * etaFine) (((M : ℝ) * spacing) * etaCoarse)
    hfineNonneg hcoarseNonneg fine_small coarse_small hsmall'

end

end YangMills.RG
