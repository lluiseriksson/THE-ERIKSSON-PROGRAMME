/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226PhysicalCutoffBoundary
import YangMills.RG.BalabanCMP116Eq220ResidualLedger

/-!
# CMP116 equation (2.26) with the (1.36) residual ledger consumed

The physical cutoff boundary previously ended at a product containing a free
real scalar called `residual`.  Here that scalar is fixed to the literal sum of
the domain weights produced by (1.36)+(2.18).  The rooted source count and the
explicit scalar allocation then absorb it, together with the Gaussian base
rate, into the single localized-volume factor printed in (2.26).

The terminal theorem therefore concludes directly with
`cmp116Eq226SourceTermWeight`.  It retains only the genuine source obligations:
the physical integrand inequalities, the rooted domain count, and the scalar
smallness budget.  No arbitrary term weight or renamed residual estimate is
present in its conclusion or interface.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace CMP116Eq214FiniteGaussianData

theorem norm_term_le_eq226SourceTermWeight_of_physicalCutoff_residualLedger
    {d M N' Nc L lieDim nDelta nY : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {Ψ Φ E : Type*} [Norm E]
    (G : CMP116Eq214FiniteGaussianData nDelta nY
      (Cube d L) Ψ Φ E lieDim)
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    {precision covariance root :
      PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
        PhysicalGaugeOneCochain d (M * N') Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond d (M * N') → PhysicalBond d (M * N') → ℝ}
    (hcert : PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight rootWeight)
    (Y0 P : Finset (Cube d L)) (Z0 : Finset (FinBox d N'))
    (psi : Ψ) (phi : Φ)
    (alpha5 outerBound sourceRate gamma2 : ℝ)
    (r : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
        CMP116CoordIndex d L lieDim → ℝ)
    (J : (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      Matrix (CMP116CoordIndex d L lieDim)
        (CMP116CoordIndex d L lieDim) ℝ)
    {E0 epsilon1 C1 alpha4 : ℝ} {q : ℕ}
    {C2 kappa1 delta kappa gk : ℝ}
    (domainMetric : Fin nY → ℕ) (domainSupport : Fin nY → Finset (FinBox d N'))
    (gapL gapCard : ℕ)
    (rootBound Calpha5 : ℝ)
    (hDeltaRadius : G.deltaRadius =
      fun _ => cmp116Eq214SigmaCauchyRadius kappa1)
    (hnormalizedGap :
      ((((gapL * M : ℕ) : ℝ) ^ 4)⁻¹ * (gapCard : ℝ)) =
        (nDelta : ℝ))
    (hYRadius : G.yRadius = fun Y =>
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa (domainMetric Y : ℝ))
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1)
    (hC1 : 0 < C1) (halpha4 : 0 < alpha4) (hM : 1 ≤ M)
    (hgk : gk ≠ 0) (hthresholdEq : G.threshold = epsilon1 / gk)
    (halpha5 : 0 ≤ alpha5)
    (hsmall : alpha5 * covNormBound < (1 : ℝ) / 2)
    (hsourceRate : 0 ≤ sourceRate)
    (hbeta : 2 *
      (cmp116Eq225SourceCoefficient (Dict.physicalRootMatrix root) alpha5 *
        sourceRate) < 1)
    (houter_nonneg : 0 ≤ outerBound) (houter_le_one : outerBound ≤ 1)
    (hgamma : 0 ≤ gamma2) (hthreshold_nonneg : 0 ≤ G.threshold)
    (houter : ∀ sigma tau x,
      ‖G.outerWeight sigma tau psi phi x‖ ≤ outerBound)
    (hinner : ∀ sigma tau x b,
      ‖G.innerWeight sigma tau psi phi x b‖ ≤
        Real.exp (∑ i, r sigma tau x i * b i))
    (hinteraction : ∀ sigma tau b,
      (G.interactionExponent sigma tau psi phi b).re +
          (gamma2 / 2) *
            (∑ e ∈ P, ‖G.bondField b e‖ ^ 2) ≤
        -((b ⬝ᵥ
          ((-(alpha5 • cmp116Eq223CoordinateProjection
            (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0))) *ᵥ b)) / 2) +
          ∑ Y : Fin nY,
            cmp116Eq220ResidualDomainWeight alpha4 delta kappa
              (domainMetric Y : ℝ))
    (hshape : ∀ sigma tau x,
      r sigma tau x = J sigma tau *ᵥ
        (cmp116Eq223CoordinateProjection
          (Dict.cmp116Eq223PhysicalLocalizedCoordinates Z0) *ᵥ x))
    (hJ : ∀ sigma tau, ‖J sigma tau‖ ^ 2 ≤ sourceRate)
    (hne : ∀ Y : Fin nY, (domainSupport Y).Nonempty)
    (hsub : ∀ Y : Fin nY, domainSupport Y ⊆ Z0)
    (hroot : ∀ i ∈ Z0,
      ∑ Y ∈ (Finset.univ.filter fun Y : Fin nY => i ∈ domainSupport Y),
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainMetric Y : ℝ) ≤ rootBound)
    (hvolumeBudget :
      rootBound +
          PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
            M d Nc (Dict.physicalRootMatrix root) alpha5
            (cmp116Eq225SourceCoefficient
              (Dict.physicalRootMatrix root) alpha5 * sourceRate) ≤
        Calpha5 * alpha5) :
    ‖(G.withPhysicalRootMatrix Dict root).toAnalyticData.term
        Y0 P psi phi‖ ≤
      cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma2 gk gapL gapCard
        Calpha5 alpha5 Z0.card domainMetric Finset.univ P := by
  let residualSum :=
    ∑ Y : Fin nY,
      cmp116Eq220ResidualDomainWeight alpha4 delta kappa
        (domainMetric Y : ℝ)
  let baseRate :=
    PhysicalGaugeCMP116Dictionary.cmp116Eq226TotalGaussianCardinalityRate
      M d Nc (Dict.physicalRootMatrix root) alpha5
      (cmp116Eq225SourceCoefficient
        (Dict.physicalRootMatrix root) alpha5 * sourceRate)
  have hterm := G.norm_term_le_of_physicalCutoff_eq226DomainGap
    Dict hcert Y0 P Z0 psi phi alpha5 outerBound sourceRate gamma2 residualSum
    r J domainMetric gapL gapCard hDeltaRadius hnormalizedGap hYRadius
    hE0 hepsilon1 hC1 halpha4 hM halpha5 hsmall hsourceRate hbeta
    houter_nonneg hgamma hthreshold_nonneg houter hinner
    (by simpa [residualSum] using hinteraction) hshape hJ
  refine hterm.trans ?_
  change
    ((outerBound *
          Real.exp
            (residualSum - gamma2 / 2 * G.threshold ^ 2 * (P.card : ℝ)) *
          Real.exp (baseRate * (Z0.card : ℝ))) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric Finset.univ) *
        cmp116Eq226GapFactor kappa1 gapL M gapCard ≤ _
  apply cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_residualLedger
    (D := (Finset.univ : Finset (Fin nY))) (P := P) (Z0 := Z0)
    domainSupport (fun Y => (domainMetric Y : ℝ)) domainMetric
    hE0.le hepsilon1.le hC1.le halpha4.le hgk hthresholdEq houter_le_one
  · intro Y _
    exact hne Y
  · intro Y _
    exact hsub Y
  · exact hroot
  · simpa [baseRate] using hvolumeBudget

end CMP116Eq214FiniteGaussianData

end

end YangMills.RG
