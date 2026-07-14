/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214FiniteGaussianMajorant
import YangMills.RG.BalabanCMP116Lemma3ResidualStages

/-!
# CMP116 equation (2.26): finite Gaussian terms through the residual stages

This module connects the literal finite-Gaussian/Cauchy majorant to the
already formalized `D`, `P`, `Z₀`, and `Z₀'` resummation stages.  The resulting
theorem has neither an abstract contour hypothesis nor a monolithic
`hbudget`: its remaining quantitative premise is the pointwise factorization
of the explicit Cauchy weight into the source weights consumed by equations
(2.29), (2.31), and (2.37).

That pointwise factorization is the live analytic estimate (2.26); this module
does not assume it under the name of the final activity bound.
-/

namespace YangMills.RG

/-- The finite-Gaussian resummation with its Cauchy majorant fixed by physical
weight bounds. -/
noncomputable def cmp116Eq214FiniteGaussianResummation
    {d M N' nDelta nY lieDim : ℕ} [NeZero M] [NeZero N']
    {ιZ0' Ψ Φ E : Type*} [Norm E]
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (gaussianData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214FiniteGaussianData nDelta nY
          (PhysicalBond d (M * N')) Ψ Φ E lieDim)
    (outerBound innerBound interactionBound :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ) :
    CMP116HResummation
      (Finset (FinBox d N'))
      (Finset (Finset (FinBox d N')))
      (Finset (PhysicalBond d (M * N')))
      (Finset (FinBox d N')) ιZ0' Ψ Φ :=
  cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
    distinguished Z0PrimeIndex
    (fun Z D P Z0 Z0p => (gaussianData Z D P Z0 Z0p).toAnalyticData)
    (fun Z D P Z0 Z0p => cmp116Eq214FiniteGaussianBoundaryMajorant
      (outerBound Z D P Z0 Z0p) (innerBound Z D P Z0 Z0p)
      (interactionBound Z D P Z0 Z0p))

/-- Equation (2.29) and the normalized residual stages turn the explicit
finite-Gaussian term estimate into the complete CMP116 Lemma-3 bound.

The only termwise analytic premise is `hfactor`, which compares the canonical
inverse-radius Cauchy weight with the product of the source residual weights.
It is the exact slot to be discharged by equations (2.16)--(2.26). -/
theorem norm_balabanCMP116H_le_of_finiteGaussian_eq229_residualStages
    {d M N' nDelta nY lieDim : ℕ} [NeZero M] [NeZero N']
    {ιZ0' ιY Ψ Φ E : Type*} [DecidableEq ιZ0'] [Norm E]
    (hp : CMP116Lemma3Parameters)
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (gaussianData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214FiniteGaussianData nDelta nY
          (PhysicalBond d (M * N')) Ψ Φ E lieDim)
    (outerBound innerBound interactionBound :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (sourceMetric : Finset (FinBox d N') → ℕ)
    (DParts :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) → Finset ιY)
    (alpha6 : ℝ)
    (eq229Metric : Finset (FinBox d N') → ιY → ℕ)
    (pWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) → ℝ)
    (z0Weight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ℝ)
    (z0PrimeWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (hDelta : ∀ Z D P Z0 Z0p i,
      0 < (gaussianData Z D P Z0 Z0p).deltaRadius i)
    (hY : ∀ Z D P Z0 Z0p i,
      0 < (gaussianData Z D P Z0 Z0p).yRadius i)
    (houter_nonneg : ∀ Z D P Z0 Z0p,
      0 ≤ outerBound Z D P Z0 Z0p)
    (houter : ∀ Z D P Z0 Z0p ψ φ sigma tau x,
      ‖(gaussianData Z D P Z0 Z0p).outerWeight sigma tau ψ φ x‖ ≤
        outerBound Z D P Z0 Z0p)
    (hinner : ∀ Z D P Z0 Z0p ψ φ sigma tau x b,
      ‖(gaussianData Z D P Z0 Z0p).innerWeight sigma tau ψ φ x b‖ ≤
        innerBound Z D P Z0 Z0p)
    (hinteraction : ∀ Z D P Z0 Z0p ψ φ sigma tau b,
      ((gaussianData Z D P Z0 Z0p).interactionExponent
        sigma tau ψ φ b).re ≤ interactionBound Z D P Z0 Z0p)
    (hEq229 : CMP116Eq229Summability
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).DIndex
      DParts alpha6 hp.delta hp.kappa eq229Metric)
    (hPsum : CMP116PResidualSummability
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).DIndex
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).PIndex pWeight)
    (hZ0sum : CMP116Z0ResidualSummability
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).DIndex
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).PIndex
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).Z0Index z0Weight)
    (hZ0PrimeSum : CMP116Z0PrimeResidualSummability
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).DIndex
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).PIndex
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).Z0Index
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).Z0PrimeIndex z0PrimeWeight)
    (halpha6 : 0 ≤ alpha6)
    (hpWeight_nonneg : ∀ Z D,
      D ∈ (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).DIndex Z → ∀ P,
      P ∈ (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).PIndex Z D → 0 ≤ pWeight Z D P)
    (hz0Weight_nonneg : ∀ Z D,
      D ∈ (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).DIndex Z → ∀ P,
      P ∈ (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).PIndex Z D → ∀ Z0,
      Z0 ∈ (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).Z0Index Z D P → 0 ≤ z0Weight Z D P Z0)
    (hfactor : ∀ Z D,
      D ∈ (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).DIndex Z → ∀ P,
      P ∈ (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).PIndex Z D → ∀ Z0,
      Z0 ∈ (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).Z0Index Z D P → ∀ Z0',
      Z0' ∈ (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).Z0PrimeIndex Z D P Z0 →
      (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
        distinguished Z0PrimeIndex gaussianData outerBound innerBound
        interactionBound).termWeight Z D P Z0 Z0' ≤
        (((((hp.C3 * hp.epsilon1) *
            balabanCMP116Lemma3Weight hp.blockScale hp.delta hp.kappa
              sourceMetric Z) *
            Finset.prod (DParts Z D)
              (cmp116Eq229Weight alpha6 hp.delta hp.kappa (eq229Metric Z))) *
            pWeight Z D P) * z0Weight Z D P Z0) *
          z0PrimeWeight Z D P Z0 Z0') :
    ∀ Z ψ φ,
      ‖balabanCMP116H
        (cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex gaussianData outerBound innerBound
          interactionBound) Z ψ φ‖ ≤
        (hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight hp.blockScale hp.delta hp.kappa
            sourceMetric Z := by
  let R := cmp116Eq214FiniteGaussianResummation domainFamily allowed ambient
    distinguished Z0PrimeIndex gaussianData outerBound innerBound
    interactionBound
  apply norm_balabanCMP116H_le_termWeightSum hp R sourceMetric
  · simpa [R, cmp116Eq214FiniteGaussianResummation] using
      cmp116Eq214CauchyMajorizedResummation_term_bound_of_finiteGaussianWeights
        domainFamily allowed ambient distinguished Z0PrimeIndex gaussianData
        outerBound innerBound interactionBound hDelta hY houter_nonneg houter
        hinner hinteraction
  · exact cmp116H_termWeightSum_le_of_eq229_of_residualStages
      hp R sourceMetric DParts alpha6 eq229Metric pWeight z0Weight z0PrimeWeight
      (by simpa [R] using hEq229)
      (by simpa [R] using hPsum)
      (by simpa [R] using hZ0sum)
      (by simpa [R] using hZ0PrimeSum)
      halpha6
      (by simpa [R] using hpWeight_nonneg)
      (by simpa [R] using hz0Weight_nonneg)
      (by simpa [R] using hfactor)

end YangMills.RG
