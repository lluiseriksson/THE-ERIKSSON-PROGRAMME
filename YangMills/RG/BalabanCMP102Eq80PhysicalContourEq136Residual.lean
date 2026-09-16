import YangMills.RG.BalabanCMP102Eq80PhysicalContourResidualAdapter

/-!
# Equation-(1.36) for the literal restricted contour residual

The indexed equation-(80) producer already proves `(1.36)` after the physical
small-field cutoff.  This file transports that theorem through the literal
restricted contour coordinate
`cmp116SourceRestrictedShiftedCoupling` and then through the centered terminal
projection.  Hence a terminal constructor need not receive a second
`hdirect : |V''| ≤ ...` premise.

No Lemma-1 residual is treated here.  That distinct source sector is kept in
`CMP116Lemma1Eq136ResidualCertificate`.
-/

namespace YangMills.RG

noncomputable section

private abbrev ContourEq136FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev ContourEq136CoarseField (Q Nc : ℕ)
    [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev ContourEq136RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  ContourEq136CoarseField Q Nc →L[ℝ]
    ContourEq136FineField M Q Nc

/-- The literal indexed contour residual satisfies `(1.36)`.  The uniform
source-coupling cap is derived from the shifted Cauchy polydisc and the
physical contour-radius cap. -/
theorem abs_cmp102Eq80PhysicalIndexedContourResidual_le_eq136
    {nDelta M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (M * (2 * Q))]
    [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (domains : Finset (CMP102Eq80SourcePi4PhysicalDomainLabel anchor))
    (contourCarrier : Finset (FinBox 4 (2 * Q)))
    (e : Fin nDelta ≃ ↥contourCarrier)
    (deltaRadius : Fin nDelta → ℝ)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hradiusCap : ∀ j, 1 + deltaRadius j ≤ radius)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (Pcut : Finset (PhysicalBond 4 (M * (2 * Q))))
    (epsilon1 gk : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hepsilon1 : 0 ≤ epsilon1) (hepsilon1_one : epsilon1 ≤ 1)
    (hgk : 0 < gk)
    (hcutoff :
      (-1 : ℂ) ^ Pcut.card *
          cmp116SmallFieldCutoff
            (cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor domains)
            (epsilon1 / gk) (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff Pcut (epsilon1 / gk)
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0)
    (K : ContourEq136FineField M Q Nc →L[ℝ]
      ContourEq136FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      ContourEq136CoarseField Q Nc →L[ℝ]
        ContourEq136CoarseField Q Nc)
    {Ahead rho rate : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : Fin nDelta → ℂ)
    (hsigma : CMP116Eq214ShiftedPolydisc nDelta deltaRadius sigma)
    (hsmallContour :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho (1 + radius)‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : ContourEq136FineField M Q Nc →
      ContourEq136CoarseField Q Nc)
    (V₀ : ContourEq136FineField M Q Nc → ℝ)
    (Pprop T : ContourEq136RectangularFieldMap M Q Nc)
    (Δπ : ContourEq136FineField M Q Nc →L[ℝ]
      ContourEq136FineField M Q Nc)
    (J : ContourEq136FineField M Q Nc)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (C Rjet sourceJetBound : ℝ)
    (hsourceJetBound : 0 ≤ sourceJetBound)
    (hC : ∀ X, cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j, j ≤ 4 →
        ‖iteratedFDeriv ℝ j V₀
          (cmp102Eq80JointRemainderInner
            D (Pprop + t • T,
              cmp109ConstrainedLinearFluctuation (L := M) gk X))‖ ≤ C)
    (hRjet : ∀ X, cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j,
        1 ≤ j → j ≤ 4 →
        ‖iteratedFDeriv ℝ j
            (fun q :
                ContourEq136RectangularFieldMap M Q Nc ×
                  ContourEq136FineField M Q Nc => q.2)
            (Pprop + t • T,
              cmp109ConstrainedLinearFluctuation (L := M) gk X)‖ +
          cmp102Eq80JointEvaluationJetMajorant D j
            (Pprop + t • T,
              cmp109ConstrainedLinearFluctuation (L := M) gk X) ≤
            Rjet ^ j)
    (hsourceJet : ∀ X, cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        max
          (cmp102Eq80JointPotentialSourceJetMajorant
            D D₃ Δπ J 4
              (Pprop + t • T,
                cmp109ConstrainedLinearFluctuation (L := M) gk X)
              C Rjet) 0 ≤ sourceJetBound)
    {cardRatio metricRatio summationRatio κcard : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 < κcard)
    (E0 C1 : ℝ) (q : ℕ) (C2 kappa1 delta kappa : ℝ)
    (hresidualRate0 :
      0 ≤ cmp102Eq80Eq136ResidualMetricRate delta kappa)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate (1 + radius) ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp
        (-(cmp102Eq80Eq136ResidualMetricRate delta kappa * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (hbudget : CMP102Eq80Eq136ThirdJetProducerBudget
      (M := M) baseCoarseCovariance sourceJetBound κcard
      delta kappa summationRatio layerWord Δ q E0 C1 C2 kappa1) :
    |cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk
        (cmp116SourcePhysicalCoordinateCochain b)| ≤
      cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
        C2 kappa1 delta kappa
          (cmp116CubeEdgeTreeMetric
            (cmp102Eq80SourcePi4IndexedLocalizationDomain
              (M := M) anchor domains i) : ℝ) := by
  have hRweak : (1 : ℝ) ≤ 1 + radius := by linarith
  have hcap : ∀ d : FinBox 4 (2 * Q),
      ‖cmp116SourceRestrictedShiftedCoupling
        contourCarrier e sigma d‖ ≤ 1 + radius := by
    intro d
    exact norm_cmp116SourceRestrictedShiftedCoupling_le_one_add_global
      contourCarrier e deltaRadius sigma hsigma hradius hradiusCap d
  simpa [cmp102Eq80PhysicalIndexedContourResidual] using
    (abs_half_inner_cmp116RadialTaylorResidualOperator_eq80IndexedPhysicalDomain_le_eq136
      anchor domains i Pcut epsilon1 gk b hepsilon1 hepsilon1_one hgk hcutoff
      K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
      (cmp116SourceRestrictedShiftedCoupling contourCarrier e sigma)
      hRweak hcap hsmallContour layerWord choice
      D D₃ V₀ Pprop T Δπ J hD hD₃ hV₀
      C Rjet sourceJetBound hsourceJetBound hC hRjet hsourceJet
      hcardRatio0 hmetricRatio0 hsummation0 hκcard
      E0 C1 q C2 kappa1 delta kappa hresidualRate0
      hsplit hcardDecay hmetricDecay hsmall hbudget)

/-- Terminal form of the same bound.  The centered `Z0` projection disappears
by the exact source-domain projection dictionary before `(1.36)` is applied. -/
theorem abs_cmp102Eq80PhysicalIndexedContourResidual_centeredRegion_le_eq136
    {nDelta M Q Nc R Δ n L lieDim : ℕ}
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
    (deltaRadius : Fin nDelta → ℝ)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hradiusCap : ∀ j, 1 + deltaRadius j ≤ radius)
    (i : Fin (CMP102Eq80SourcePi4DomainCount anchor domains))
    (Pcut : Finset (PhysicalBond 4 (M * (2 * Q))))
    (epsilon1 gk : ℝ)
    (b : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1))
    (hepsilon1 : 0 ≤ epsilon1) (hepsilon1_one : epsilon1 ≤ 1)
    (hgk : 0 < gk)
    (hcutoff :
      (-1 : ℂ) ^ Pcut.card *
          cmp116SmallFieldCutoff
            (cmp102Eq80SourcePi4PhysicalY0 (M := M) anchor domains)
            (epsilon1 / gk) (cmp116SourcePhysicalCoordinateCochain b) *
          cmp116LargeFieldCutoff Pcut (epsilon1 / gk)
            (cmp116SourcePhysicalCoordinateCochain b) ≠ 0)
    (K : ContourEq136FineField M Q Nc →L[ℝ]
      ContourEq136FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      ContourEq136CoarseField Q Nc →L[ℝ]
        ContourEq136CoarseField Q Nc)
    {Ahead rho rate : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : Fin nDelta → ℂ)
    (hsigma : CMP116Eq214ShiftedPolydisc nDelta deltaRadius sigma)
    (hsmallContour :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho (1 + radius)‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : ContourEq136FineField M Q Nc →
      ContourEq136CoarseField Q Nc)
    (V₀ : ContourEq136FineField M Q Nc → ℝ)
    (Pprop T : ContourEq136RectangularFieldMap M Q Nc)
    (Δπ : ContourEq136FineField M Q Nc →L[ℝ]
      ContourEq136FineField M Q Nc)
    (J : ContourEq136FineField M Q Nc)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (C Rjet sourceJetBound : ℝ)
    (hsourceJetBound : 0 ≤ sourceJetBound)
    (hC : ∀ X, cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j, j ≤ 4 →
        ‖iteratedFDeriv ℝ j V₀
          (cmp102Eq80JointRemainderInner
            D (Pprop + t • T,
              cmp109ConstrainedLinearFluctuation (L := M) gk X))‖ ≤ C)
    (hRjet : ∀ X, cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ j,
        1 ≤ j → j ≤ 4 →
        ‖iteratedFDeriv ℝ j
            (fun q :
                ContourEq136RectangularFieldMap M Q Nc ×
                  ContourEq136FineField M Q Nc => q.2)
            (Pprop + t • T,
              cmp109ConstrainedLinearFluctuation (L := M) gk X)‖ +
          cmp102Eq80JointEvaluationJetMajorant D j
            (Pprop + t • T,
              cmp109ConstrainedLinearFluctuation (L := M) gk X) ≤
            Rjet ^ j)
    (hsourceJet : ∀ X, cmp98SourceFieldSupNorm X ≤ epsilon1 / gk →
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        max
          (cmp102Eq80JointPotentialSourceJetMajorant
            D D₃ Δπ J 4
              (Pprop + t • T,
                cmp109ConstrainedLinearFluctuation (L := M) gk X)
              C Rjet) 0 ≤ sourceJetBound)
    {cardRatio metricRatio summationRatio κcard : ℝ}
    (hcardRatio0 : 0 ≤ cardRatio)
    (hmetricRatio0 : 0 ≤ metricRatio)
    (hsummation0 : 0 ≤ summationRatio)
    (hκcard : 0 < κcard)
    (E0 C1 : ℝ) (q : ℕ) (C2 kappa1 delta kappa : ℝ)
    (hresidualRate0 :
      0 ≤ cmp102Eq80Eq136ResidualMetricRate delta kappa)
    (hsplit :
      cmp102Eq80PhysicalFineHeadTailWalkRatio
          (M := M) baseCoarseCovariance Ahead rho rate (1 + radius) ≤
        cardRatio * (metricRatio * summationRatio))
    (hcardDecay :
      cardRatio ≤ Real.exp (-(κcard * 10000)))
    (hmetricDecay :
      metricRatio ≤ Real.exp
        (-(cmp102Eq80Eq136ResidualMetricRate delta kappa * 10000)))
    (hsmall :
      ((cmp116SourcePi4TerminalBranching Δ : ℕ) : ℝ) *
        summationRatio < 1)
    (hbudget : CMP102Eq80Eq136ThirdJetProducerBudget
      (M := M) baseCoarseCovariance sourceJetBound κcard
      delta kappa summationRatio layerWord Δ q E0 C1 C2 kappa1) :
    let Z0 := cmp102Eq80SourcePi4CenteredRegion anchor domains P
    |cmp102Eq80PhysicalIndexedContourResidual
        anchor domains contourCarrier e i K hc hmass hK
        baseCoarseCovariance sigma layerWord choice
        D D₃ V₀ Pprop T Δπ J gk
        (physicalBondProjection
          (PhysicalGaugeCMP116Dictionary.cmp116Eq223PhysicalInteriorBonds Z0)
          (cmp116SourcePhysicalCoordinateCochain b))| ≤
      cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
        C2 kappa1 delta kappa
          (cmp116CubeEdgeTreeMetric
            (cmp102Eq80SourcePi4IndexedLocalizationDomain
              (M := M) anchor domains i) : ℝ) := by
  dsimp only
  rw [cmp102Eq80PhysicalIndexedContourResidual_centeredRegion
    Dict anchor domains P contourCarrier e i K hc hmass hK
    baseCoarseCovariance sigma layerWord choice
    D D₃ V₀ Pprop T Δπ J gk]
  exact abs_cmp102Eq80PhysicalIndexedContourResidual_le_eq136
    anchor domains contourCarrier e deltaRadius radius hradius hradiusCap
    i Pcut epsilon1 gk b hepsilon1 hepsilon1_one hgk hcutoff
    K hc hmass hK baseCoarseCovariance
    hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
    sigma hsigma hsmallContour layerWord choice
    D D₃ V₀ Pprop T Δπ J hD hD₃ hV₀
    C Rjet sourceJetBound hsourceJetBound hC hRjet hsourceJet
    hcardRatio0 hmetricRatio0 hsummation0 hκcard
    E0 C1 q C2 kappa1 delta kappa hresidualRate0
    hsplit hcardDecay hmetricDecay hsmall hbudget

end

end YangMills.RG
