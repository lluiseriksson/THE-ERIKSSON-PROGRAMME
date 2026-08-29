import YangMills.RG.BalabanCMP99Eq342CommonAmplitude
import YangMills.RG.BalabanCMP99Eq342SourceLocalizedGreenCertificate
import YangMills.RG.FinitePiLpBlockLocalizedSupMonotone

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Scalar assembler for a source-localized CMP99 (3.42) certificate

This theorem only assembles four already-proved literal action bounds.  It
does not produce any action, Green, coercivity estimate or scale-uniform
constant.  Keeping it generic makes the positive- and zero-depth physical
branches share exactly one amplitude-enlargement argument.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ} [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Four literal per-depth action bounds with one common rate assemble into
the exact source-localized CMP99 (3.42) record. -/
theorem cmp99Eq342SourceLocalizedGreenCertificate_of_actionBounds
    {depth : ℕ}
    {Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))}
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    {rho : SUNAdjointModel Nc}
    {U : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc}
    {spacing : ℝ}
    {A : GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
        (SUNLieCoord Nc)}
    {c : ℝ} {hc : 0 < c} {hAcoer : IsCoerciveCLM A c}
    {Avalue Aleft Aright Alaplacian rate : ℝ}
    (hvalue_nonneg : 0 ≤ Avalue) (hleft_nonneg : 0 ≤ Aleft)
    (hright_nonneg : 0 ≤ Aright) (hlaplacian_nonneg : 0 ≤ Alaplacian)
    (hrate : 0 < rate)
    (hvalue : FinitePiLpTypedBlockLocalizedSupBound
      (cmp99RegionalDirichletGreen Omega A hc hAcoer)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (Avalue * (L ^ (depth + 1) : ℝ) ^ 2) rate)
    (hleft : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).comp
        (cmp99RegionalDirichletGreen Omega A hc hAcoer))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      finBoxDist (Aleft * (L ^ (depth + 1) : ℝ)) rate)
    (hright : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99RegionalDirichletGreen Omega A hc hAcoer).comp
        (cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing).adjoint)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (Aright * (L ^ (depth + 1) : ℝ)) rate)
    (hlaplacian : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing).comp
        (cmp99RegionalDirichletGreen Omega A hc hAcoer))
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist Alaplacian rate) :
    CMP99Eq342SourceLocalizedGreenCertificate
      (L := L) (K := K) (Q := Q) (Nc := Nc)
      depth Omega rho U spacing A c hc hAcoer
      (cmp99Eq342CommonAmplitude Avalue Aleft Aright Alaplacian) rate := by
  have hB0 : 0 < cmp99Eq342CommonAmplitude
      Avalue Aleft Aright Alaplacian :=
    cmp99Eq342CommonAmplitude_pos hvalue_nonneg hleft_nonneg
      hright_nonneg hlaplacian_nonneg
  refine {
    B0_pos := hB0
    delta0_pos := hrate
    value_bound := ?_
    left_derivative_bound := ?_
    right_adjoint_derivative_bound := ?_
    laplacian_bound := ?_
  }
  · apply finitePiLpTypedBlockLocalizedSupBound_mono hvalue
    · exact mul_le_mul_of_nonneg_right
        (le_cmp99Eq342CommonAmplitude_value hvalue_nonneg hleft_nonneg
          hright_nonneg hlaplacian_nonneg)
        (sq_nonneg (L ^ (depth + 1) : ℝ))
    · exact hrate
    · exact le_rfl
  · apply finitePiLpTypedBlockLocalizedSupBound_mono hleft
    · exact mul_le_mul_of_nonneg_right
        (le_cmp99Eq342CommonAmplitude_left hvalue_nonneg hleft_nonneg
          hright_nonneg hlaplacian_nonneg) (by positivity)
    · exact hrate
    · exact le_rfl
  · apply finitePiLpTypedBlockLocalizedSupBound_mono hright
    · exact mul_le_mul_of_nonneg_right
        (le_cmp99Eq342CommonAmplitude_right hvalue_nonneg hleft_nonneg
          hright_nonneg hlaplacian_nonneg) (by positivity)
    · exact hrate
    · exact le_rfl
  · apply finitePiLpTypedBlockLocalizedSupBound_mono hlaplacian
    · exact le_cmp99Eq342CommonAmplitude_laplacian
        hvalue_nonneg hleft_nonneg hright_nonneg hlaplacian_nonneg
    · exact hrate
    · exact le_rfl

end

end YangMills.RG
