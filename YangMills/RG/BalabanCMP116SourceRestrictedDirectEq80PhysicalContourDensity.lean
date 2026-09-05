import YangMills.RG.BalabanCMP102Eq80PhysicalContourResidualAdapter
import YangMills.RG.BalabanCMP116SourceRestrictedDirectPhysicalContourDensity

namespace YangMills.RG

noncomputable section

private abbrev DirectEq80FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev DirectEq80CoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev DirectEq80RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  DirectEq80CoarseField Q Nc →L[ℝ] DirectEq80FineField M Q Nc

private abbrev DirectEq80Endomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

namespace CMP116Eq214PhysicalContourDensity

/-- Source-specialized non-circular CMP116 contour density whose potential
families are the canonically indexed fixed Hessian and total Taylor residual
of the literal coupling-scaled CMP102 equation-(80) domain contribution.

Unlike `ofSourcePi4RestrictedPhysicalContour`, this endpoint does not receive
`quadratic` or `remainder` as arguments.  It uses every canonical source
domain, the centered source region as `Z0`, and the restricted complex
coupling coordinate. -/
def ofSourcePi4RestrictedEq80PhysicalContour
    {nDelta M Q Nc R Δ L lieDim n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    [NeZero L] [NeZero lieDim]
    {Site : Type*} {Psi Phi : Site → Type*}
    (spectatorSupport fluctuationSupport : Finset Site)
    (deltaRadius : Fin nDelta → ℝ)
    (Dict : PhysicalGaugeCMP116Dictionary
      4 (M * (2 * Q)) Nc 4 L lieDim)
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (yRadius : Fin (CMP102Eq80SourcePi4DomainCount anchor domains) → ℝ)
    (P : Finset (PhysicalBond 4 (M * (2 * Q))))
    (threshold : ℝ)
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (hcarrier : contourCarrier ⊆ cmp116SourceSigmaZero anchor)
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K root : DirectEq80Endomorphism M Q Nc)
    (baseCoarseCovariance :
      DirectEq80CoarseField Q Nc →L[ℝ]
        DirectEq80CoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : DirectEq80FineField M Q Nc →
      DirectEq80CoarseField Q Nc)
    (V₀ : DirectEq80FineField M Q Nc → ℝ)
    (Pprop T : DirectEq80RectangularFieldMap M Q Nc)
    (Δπ : DirectEq80FineField M Q Nc →L[ℝ]
      DirectEq80FineField M Q Nc)
    (J : DirectEq80FineField M Q Nc)
    (gk : ℝ)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    {Ahead rho rate radius : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (hradius : 0 ≤ radius)
    (hradiusCap :
      ∀ i, 1 + deltaRadius i ≤ radius)
    (hseries :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho (1 + radius)‖ < 1)
    (hneumann :
      (@norm
        (Matrix
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
        Matrix.linftyOpNormedRing.toNorm
        (cmp116PhysicalEndomorphismComplexMatrix K)) *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Δ Ahead rho rate radius (1 + radius) < 1) :
    CMP116Eq214PhysicalContourDensity nDelta
      (CMP102Eq80SourcePi4DomainCount anchor domains)
      (PhysicalBond 4 (M * (2 * Q))) Site Psi Phi
      (SUNLieCoord Nc) (Nc ^ 2 - 1) :=
  ofSourcePi4RestrictedPhysicalContour
    spectatorSupport fluctuationSupport deltaRadius yRadius
    Dict Finset.univ
    (fun sigma _psi _phi i B =>
      cmp102Eq80PhysicalIndexedContourFixedHessian
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk B)
    (fun sigma _psi _phi i B =>
      cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk B)
    threshold anchor contourCarrier hcarrier e
    (cmp102Eq80SourcePi4CenteredRegion anchor domains P)
    K root hsourceRange hfiniteRange hc hmass hK hD
    hAhead hrho hrate hgeom Cert htri hΔ hΔ1
    hradius hradiusCap hseries hneumann

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
