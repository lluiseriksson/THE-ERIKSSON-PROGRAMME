import YangMills.RG.BalabanCMP102Eq80PhysicalIndexedEq136Residual
import YangMills.RG.BalabanCMP116SourceRestrictedPhysicalContourDensity

namespace YangMills.RG

noncomputable section

private abbrev ContourResidualFineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev ContourResidualCoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev ContourResidualRectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  ContourResidualCoarseField Q Nc →L[ℝ]
    ContourResidualFineField M Q Nc

/-- Proof-independent fixed Hessian for one canonically indexed literal
equation-(80) domain contribution after the physical coupling substitution.
The final field argument is retained only because the CMP116 quadratic-family
interface is field-indexed; the fixed Hessian itself does not depend on it. -/
noncomputable def cmp102Eq80PhysicalIndexedContourFixedHessian
    {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (K : ContourResidualFineField M Q Nc →L[ℝ]
      ContourResidualFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      ContourResidualCoarseField Q Nc →L[ℝ]
        ContourResidualCoarseField Q Nc)
    (sigma : Fin nDelta → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : ContourResidualFineField M Q Nc →
      ContourResidualCoarseField Q Nc)
    (V₀ : ContourResidualFineField M Q Nc → ℝ)
    (Pprop T : ContourResidualRectangularFieldMap M Q Nc)
    (Δπ : ContourResidualFineField M Q Nc →L[ℝ]
      ContourResidualFineField M Q Nc)
    (J : ContourResidualFineField M Q Nc)
    (gk : ℝ) (_B : ContourResidualFineField M Q Nc) :
    ContourResidualFineField M Q Nc →L[ℝ]
      ContourResidualFineField M Q Nc :=
  let Y :=
    cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor domains i
  let f : ContourResidualFineField M Q Nc → ℝ := fun A =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
      layerWord choice D D₃ V₀ Pprop T Δπ J A Y.blocks
  let PY := physicalBondProjection Y.bondSupport
  PY.comp ((cmp102Eq80CouplingScaledFixedHessian gk f).comp PY)

/-- Exact adapter from the restricted CMP116 contour coordinate to the
indexed literal equation-(80) Taylor residual.  The input field is projected
to the selected source domain inside the definition. -/
noncomputable def cmp102Eq80PhysicalIndexedContourResidual
    {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (K : ContourResidualFineField M Q Nc →L[ℝ]
      ContourResidualFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      ContourResidualCoarseField Q Nc →L[ℝ]
        ContourResidualCoarseField Q Nc)
    (sigma : Fin nDelta → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : ContourResidualFineField M Q Nc →
      ContourResidualCoarseField Q Nc)
    (V₀ : ContourResidualFineField M Q Nc → ℝ)
    (Pprop T : ContourResidualRectangularFieldMap M Q Nc)
    (Δπ : ContourResidualFineField M Q Nc →L[ℝ]
      ContourResidualFineField M Q Nc)
    (J : ContourResidualFineField M Q Nc)
    (gk : ℝ) (B : ContourResidualFineField M Q Nc) : ℝ :=
  let Y :=
    cmp102Eq80SourcePi4IndexedLocalizationDomain
      (M := M) anchor domains i
  cmp102Eq80PhysicalIndexedCouplingScaledResidual
    anchor domains i K hc hmass hK baseCoarseCovariance
    (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
    layerWord choice D D₃ V₀ Pprop T Δπ J gk
    (physicalBondProjection Y.bondSupport B)

/-- The contour adapter is unchanged if its input has first been localized to
the canonical centered region.  Thus the terminal `P_Z0` projection and the
literal per-domain projection do not introduce a second field dictionary. -/
theorem cmp102Eq80PhysicalIndexedContourResidual_centeredRegion
    {nDelta M Q Nc R n L lieDim : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero L] [NeZero lieDim]
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (K : ContourResidualFineField M Q Nc →L[ℝ]
      ContourResidualFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      ContourResidualCoarseField Q Nc →L[ℝ]
        ContourResidualCoarseField Q Nc)
    (sigma : Fin nDelta → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : ContourResidualFineField M Q Nc →
      ContourResidualCoarseField Q Nc)
    (V₀ : ContourResidualFineField M Q Nc → ℝ)
    (Pprop T : ContourResidualRectangularFieldMap M Q Nc)
    (Δπ : ContourResidualFineField M Q Nc →L[ℝ]
      ContourResidualFineField M Q Nc)
    (J : ContourResidualFineField M Q Nc)
    (gk : ℝ) (B : ContourResidualFineField M Q Nc) :
    let Z0 := cmp102Eq80SourcePi4CenteredRegion anchor domains P
    cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          B) =
      cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk B := by
  dsimp only
  unfold cmp102Eq80PhysicalIndexedContourResidual
  simpa only using
    congrArg
      (fun X =>
        cmp102Eq80PhysicalIndexedCouplingScaledResidual
          anchor domains i K hc hmass hK baseCoarseCovariance
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
          layerWord choice D D₃ V₀ Pprop T Δπ J gk X)
      (physicalBondProjection_indexedSourceDomain_centeredRegion
        Dict anchor domains P i B)

/-- The projected proof-independent Hessian and total residual reconstruct
the literal coupling-scaled equation-(80) domain potential exactly.  The
regularity and normalization hypotheses are those proved by the existing
physical FTC producers; they are not stored in either total definition. -/
theorem
    cmp116Eq142PhysicalPotentialTerm_indexedContour_eq_couplingScaled
    {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (K : ContourResidualFineField M Q Nc →L[ℝ]
      ContourResidualFineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      ContourResidualCoarseField Q Nc →L[ℝ]
        ContourResidualCoarseField Q Nc)
    (sigma : Fin nDelta → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : ContourResidualFineField M Q Nc →
      ContourResidualCoarseField Q Nc)
    (V₀ : ContourResidualFineField M Q Nc → ℝ)
    (Pprop T : ContourResidualRectangularFieldMap M Q Nc)
    (Δπ : ContourResidualFineField M Q Nc →L[ℝ]
      ContourResidualFineField M Q Nc)
    (J : ContourResidualFineField M Q Nc)
    (gk : ℝ)
    (hf : ContDiff ℝ 2 (fun A : ContourResidualFineField M Q Nc =>
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
        layerWord choice D D₃ V₀ Pprop T Δπ J A
        (cmp102Eq80SourcePi4IndexedLocalizationDomain
          (M := M) anchor domains i).blocks))
    (hf0 :
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
        anchor K hc hmass hK baseCoarseCovariance
        (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
        layerWord choice D D₃ V₀ Pprop T Δπ J 0
        (cmp102Eq80SourcePi4IndexedLocalizationDomain
          (M := M) anchor domains i).blocks = 0)
    (hdf0 :
      fderiv ℝ (fun A : ContourResidualFineField M Q Nc =>
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
          layerWord choice D D₃ V₀ Pprop T Δπ J A
          (cmp102Eq80SourcePi4IndexedLocalizationDomain
            (M := M) anchor domains i).blocks) 0 = 0)
    (B : ContourResidualFineField M Q Nc) :
    cmp116Eq142PhysicalPotentialTerm
        (fun j =>
          cmp102Eq80PhysicalIndexedContourFixedHessian
            anchor domains contourCarrier e j K hc hmass hK
            baseCoarseCovariance sigma layerWord choice
            D D₃ V₀ Pprop T Δπ J gk)
        (fun j =>
          cmp102Eq80PhysicalIndexedContourResidual
            anchor domains contourCarrier e j K hc hmass hK
            baseCoarseCovariance sigma layerWord choice
            D D₃ V₀ Pprop T Δπ J gk)
        i B =
      let Y := cmp102Eq80SourcePi4IndexedLocalizationDomain
        (M := M) anchor domains i
      let f : ContourResidualFineField M Q Nc → ℝ := fun A =>
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
          layerWord choice D D₃ V₀ Pprop T Δπ J A Y.blocks
      cmp102Eq80CouplingScaledPotential gk f
        (physicalBondProjection Y.bondSupport B) := by
  dsimp only
  let Y := cmp102Eq80SourcePi4IndexedLocalizationDomain
    (M := M) anchor domains i
  let f : ContourResidualFineField M Q Nc → ℝ := fun A =>
    cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
      anchor K hc hmass hK baseCoarseCovariance
      (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
      layerWord choice D D₃ V₀ Pprop T Δπ J A Y.blocks
  let PY :
      ContourResidualFineField M Q Nc →L[ℝ]
        ContourResidualFineField M Q Nc :=
    physicalBondProjection (Nc := Nc) Y.bondSupport
  change
    (1 / 2 : ℝ) *
        inner ℝ B
          (PY ((cmp102Eq80CouplingScaledFixedHessian gk f)
            (PY B))) +
      cmp102Eq80CouplingScaledTotalTaylorResidual gk f (PY B) =
        cmp102Eq80CouplingScaledPotential gk f (PY B)
  rw [
    PhysicalGaugeCMP116Dictionary.inner_physicalBondProjection_right_eq_left]
  exact
    (cmp102Eq80CouplingScaledPotential_eq_fixedHessian_add_totalResidual
      gk f (by simpa [f, Y] using hf)
      (by simpa [f, Y] using hf0)
      (by simpa [f, Y] using hdf0) (PY B)).symm

end

end YangMills.RG
