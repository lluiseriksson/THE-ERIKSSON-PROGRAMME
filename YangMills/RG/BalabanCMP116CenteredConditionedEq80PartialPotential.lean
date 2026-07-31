import YangMills.RG.BalabanCMP102Eq80PhysicalContourEq136Residual
import YangMills.RG.BalabanCMP116PartialResidualAssembly

/-!
# The partial centered CMP116 potential from equation (80)

This file installs the literal equation-(80) fixed Hessian and Taylor
residual in the function types consumed by the centered conditioned
equation-(2.26) source.  The separately reindexed Lemma-1 residual is added
to both the total activity and the residual, so it cancels exactly from the
quadratic core.

No `TermSource`, equation-(1.36) proof, scale dictionary, or contour estimate
is accepted as hidden data here.  The only source sector not constructed by
the equation-(80) producer is the explicitly named
`CMP116Lemma1Eq136ResidualCertificate`.
-/

namespace YangMills.RG

noncomputable section

private abbrev Eq80PartialFineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev Eq80PartialCoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev Eq80PartialRectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  Eq80PartialCoarseField Q Nc →L[ℝ] Eq80PartialFineField M Q Nc

private abbrev Eq80PartialBond (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PhysicalBond 4 (M * (2 * Q))

private abbrev Eq80PartialField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The literal equation-(80) domain potential, expressed as its fixed
Hessian term plus its total Taylor residual. -/
noncomputable def cmp102Eq80PhysicalIndexedContourTotal
    {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K : Eq80PartialField M Q Nc →L[ℝ] Eq80PartialField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      Eq80PartialCoarseField Q Nc →L[ℝ] Eq80PartialCoarseField Q Nc)
    (sigma : Fin nDelta → ℂ)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : Eq80PartialFineField M Q Nc → Eq80PartialCoarseField Q Nc)
    (V₀ : Eq80PartialFineField M Q Nc → ℝ)
    (Pprop T : Eq80PartialRectangularFieldMap M Q Nc)
    (Δπ : Eq80PartialFineField M Q Nc →L[ℝ]
      Eq80PartialFineField M Q Nc)
    (J : Eq80PartialFineField M Q Nc)
    (gk : ℝ) :
    Fin (CMP102Eq80SourcePi4DomainCount anchor domains) →
      Eq80PartialField M Q Nc → ℝ :=
  cmp116Eq142PhysicalPotentialTerm
    (fun i =>
      cmp102Eq80PhysicalIndexedContourFixedHessian
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk)
    (fun i =>
      cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk)

/-- The terminal total activity for the partial source assembly.  Spectator
and fluctuation fields are present with their literal terminal types; the
equation-(80) contribution is independent of them at this source stage. -/
noncomputable def cmp116CenteredConditionedEq80PartialTotal
    {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport : Finset (Eq80PartialBond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K : Eq80PartialField M Q Nc →L[ℝ] Eq80PartialField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      Eq80PartialCoarseField Q Nc →L[ℝ] Eq80PartialCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : Eq80PartialFineField M Q Nc → Eq80PartialCoarseField Q Nc)
    (V₀ : Eq80PartialFineField M Q Nc → ℝ)
    (Pprop T : Eq80PartialRectangularFieldMap M Q Nc)
    (Δπ : Eq80PartialFineField M Q Nc →L[ℝ]
      Eq80PartialFineField M Q Nc)
    (J : Eq80PartialFineField M Q Nc)
    (gk : ℝ)
    (epsilon1 C1 : ℝ) (q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (lemma1 : CMP116Lemma1Eq136ResidualCertificate
      (E := Eq80PartialField M Q Nc)
      (fun i =>
        (cmp116CubeEdgeTreeMetric
          (cmp102Eq80SourcePi4IndexedLocalizationDomain
            (M := M) anchor domains i) : ℝ))
      epsilon1 C1 M q C2 kappa1 delta kappa) :
    (Fin nDelta → ℂ) →
      RestrictedField spectatorSupport (fun _ => SUNLieCoord Nc) →
      RestrictedField fluctuationSupport (fun _ => SUNLieCoord Nc) →
      Fin (CMP102Eq80SourcePi4DomainCount anchor domains) →
      Eq80PartialField M Q Nc → ℝ :=
  fun sigma _psi _phi =>
    cmp116PartialResidualTotal
      (cmp102Eq80PhysicalIndexedContourTotal
        anchor domains contourCarrier e K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk)
      lemma1.residual

/-- The terminal residual for the partial source assembly. -/
noncomputable def cmp116CenteredConditionedEq80PartialResidual
    {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport : Finset (Eq80PartialBond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K : Eq80PartialField M Q Nc →L[ℝ] Eq80PartialField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      Eq80PartialCoarseField Q Nc →L[ℝ] Eq80PartialCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : Eq80PartialFineField M Q Nc → Eq80PartialCoarseField Q Nc)
    (V₀ : Eq80PartialFineField M Q Nc → ℝ)
    (Pprop T : Eq80PartialRectangularFieldMap M Q Nc)
    (Δπ : Eq80PartialFineField M Q Nc →L[ℝ]
      Eq80PartialFineField M Q Nc)
    (J : Eq80PartialFineField M Q Nc)
    (gk : ℝ)
    (epsilon1 C1 : ℝ) (q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (lemma1 : CMP116Lemma1Eq136ResidualCertificate
      (E := Eq80PartialField M Q Nc)
      (fun i =>
        (cmp116CubeEdgeTreeMetric
          (cmp102Eq80SourcePi4IndexedLocalizationDomain
            (M := M) anchor domains i) : ℝ))
      epsilon1 C1 M q C2 kappa1 delta kappa) :
    (Fin nDelta → ℂ) →
      RestrictedField spectatorSupport (fun _ => SUNLieCoord Nc) →
      RestrictedField fluctuationSupport (fun _ => SUNLieCoord Nc) →
      Fin (CMP102Eq80SourcePi4DomainCount anchor domains) →
      Eq80PartialField M Q Nc → ℝ :=
  fun sigma _psi _phi =>
    cmp116PartialResidual
      (fun i =>
        cmp102Eq80PhysicalIndexedContourResidual
          anchor domains contourCarrier e i K hc hmass hK
          baseCoarseCovariance sigma layerWord choice
          D D₃ V₀ Pprop T Δπ J gk)
      lemma1.residual

/-- The Lemma-1 contribution cancels exactly from the terminal quadratic
core.  This theorem is independent of every Lemma-1 analytic estimate. -/
theorem cmp116Eq142PhysicalQuadraticCore_centeredConditionedEq80Partial
    {nDelta M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (spectatorSupport fluctuationSupport : Finset (Eq80PartialBond M Q))
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (K : Eq80PartialField M Q Nc →L[ℝ] Eq80PartialField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      Eq80PartialCoarseField Q Nc →L[ℝ] Eq80PartialCoarseField Q Nc)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : Eq80PartialFineField M Q Nc → Eq80PartialCoarseField Q Nc)
    (V₀ : Eq80PartialFineField M Q Nc → ℝ)
    (Pprop T : Eq80PartialRectangularFieldMap M Q Nc)
    (Δπ : Eq80PartialFineField M Q Nc →L[ℝ]
      Eq80PartialFineField M Q Nc)
    (J : Eq80PartialFineField M Q Nc)
    (gk : ℝ)
    (epsilon1 C1 : ℝ) (q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (lemma1 : CMP116Lemma1Eq136ResidualCertificate
      (E := Eq80PartialField M Q Nc)
      (fun i =>
        (cmp116CubeEdgeTreeMetric
          (cmp102Eq80SourcePi4IndexedLocalizationDomain
            (M := M) anchor domains i) : ℝ))
      epsilon1 C1 M q C2 kappa1 delta kappa)
    (sigma : Fin nDelta → ℂ)
    (psi : RestrictedField spectatorSupport (fun _ => SUNLieCoord Nc))
    (phi : RestrictedField fluctuationSupport (fun _ => SUNLieCoord Nc))
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (B : Eq80PartialField M Q Nc) :
    cmp116Eq142PhysicalQuadraticCore
        (cmp116CenteredConditionedEq80PartialTotal
          spectatorSupport fluctuationSupport anchor domains
          contourCarrier e K hc hmass hK baseCoarseCovariance
          layerWord choice D D₃ V₀ Pprop T Δπ J gk
          epsilon1 C1 q C2 kappa1 delta kappa lemma1 sigma psi phi)
        (cmp116CenteredConditionedEq80PartialResidual
          spectatorSupport fluctuationSupport anchor domains
          contourCarrier e K hc hmass hK baseCoarseCovariance
          layerWord choice D D₃ V₀ Pprop T Δπ J gk
          epsilon1 C1 q C2 kappa1 delta kappa lemma1 sigma psi phi)
        i B =
      cmp116Eq142PhysicalQuadraticCore
        (cmp102Eq80PhysicalIndexedContourTotal
          anchor domains contourCarrier e K hc hmass hK
          baseCoarseCovariance sigma layerWord choice
          D D₃ V₀ Pprop T Δπ J gk)
        (fun j =>
          cmp102Eq80PhysicalIndexedContourResidual
            anchor domains contourCarrier e j K hc hmass hK
            baseCoarseCovariance sigma layerWord choice
            D D₃ V₀ Pprop T Δπ J gk)
        i B := by
  exact cmp116Eq142PhysicalQuadraticCore_partialResidual
    (cmp102Eq80PhysicalIndexedContourTotal
      anchor domains contourCarrier e K hc hmass hK
      baseCoarseCovariance sigma layerWord choice
      D D₃ V₀ Pprop T Δπ J gk)
    (fun j =>
      cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e j K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk)
    lemma1.residual i B

end

end YangMills.RG
