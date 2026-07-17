/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214CauchyMajorant
import YangMills.RG.BalabanCMP116Eq214FiniteGaussianData

/-!
# CMP116 equation (2.26): finite-Gaussian physical majorants

This module removes the abstract nested-contour hypothesis from the public
finite-Gaussian estimate.  The boundary majorant is fixed to the product of
three source-facing quantities:

* a uniform bound for the outer Wilson weight;
* a uniform bound for the inner Wilson weight;
* an upper bound for the real part of the interaction exponent.

The cutoff factors are contractions and both Gaussian laws are probability
measures, so these three estimates imply the complete nested Cauchy boundary
condition.  The remaining summation budget is precisely the quantitative
content still required from CMP116 equations (2.16)--(2.26).
-/

namespace YangMills.RG

/-- Canonical contour majorant produced by the three physical uniform bounds. -/
noncomputable def cmp116Eq214FiniteGaussianBoundaryMajorant
    (outerBound innerBound interactionBound : ℝ) : ℝ :=
  outerBound * (innerBound * Real.exp interactionBound)

/-- For concrete finite Gaussian laws, uniform bounds on the two Wilson
weights and interaction exponent discharge the generic pointwise `hterm`
obligation.  No measure or nested-contour premise remains. -/
theorem cmp116Eq214CauchyMajorizedResummation_term_bound_of_finiteGaussianWeights
    {d M N' nDelta nY lieDim : ℕ} [NeZero M] [NeZero N']
    {ιZ0' Ψ Φ E : Type*} [DecidableEq ιZ0'] [Norm E]
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
        sigma tau ψ φ b).re ≤ interactionBound Z D P Z0 Z0p) :
    ∀ Z x,
      x ∈ cmp116HIndexFinset
        (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex
          (fun Z D P Z0 Z0p =>
            (gaussianData Z D P Z0 Z0p).toAnalyticData)
          (fun Z D P Z0 Z0p => cmp116Eq214FiniteGaussianBoundaryMajorant
            (outerBound Z D P Z0 Z0p) (innerBound Z D P Z0 Z0p)
            (interactionBound Z D P Z0 Z0p))) Z →
      ∀ ψ φ,
        ‖(cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex
          (fun Z D P Z0 Z0p =>
            (gaussianData Z D P Z0 Z0p).toAnalyticData)
          (fun Z D P Z0 Z0p => cmp116Eq214FiniteGaussianBoundaryMajorant
            (outerBound Z D P Z0 Z0p) (innerBound Z D P Z0 Z0p)
            (interactionBound Z D P Z0 Z0p))).summand
              Z x.1.1 x.1.2 x.2.1 x.2.2 ψ φ‖ ≤
          (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
            distinguished Z0PrimeIndex
            (fun Z D P Z0 Z0p =>
              (gaussianData Z D P Z0 Z0p).toAnalyticData)
            (fun Z D P Z0 Z0p => cmp116Eq214FiniteGaussianBoundaryMajorant
              (outerBound Z D P Z0 Z0p) (innerBound Z D P Z0 Z0p)
              (interactionBound Z D P Z0 Z0p))).termWeight
                Z x.1.1 x.1.2 x.2.1 x.2.2 := by
  apply cmp116Eq214CauchyMajorizedResummation_term_bound
    domainFamily allowed ambient distinguished Z0PrimeIndex
    (fun Z D P Z0 Z0p => (gaussianData Z D P Z0 Z0p).toAnalyticData)
    (fun Z D P Z0 Z0p => cmp116Eq214FiniteGaussianBoundaryMajorant
      (outerBound Z D P Z0 Z0p) (innerBound Z D P Z0 Z0p)
      (interactionBound Z D P Z0 Z0p))
  · exact hDelta
  · exact hY
  · intro Z D P Z0 Z0p ψ φ
    exact (gaussianData Z D P Z0 Z0p).nestedCauchyBoundaryBound_of_uniformWeights
      (cmp116Eq214SmallFieldBondCarrier ambient distinguished D) P ψ φ
      (outerBound Z D P Z0 Z0p) (innerBound Z D P Z0 Z0p)
      (interactionBound Z D P Z0 Z0p)
      (houter_nonneg Z D P Z0 Z0p)
      (houter Z D P Z0 Z0p ψ φ)
      (hinner Z D P Z0 Z0p ψ φ)
      (hinteraction Z D P Z0 Z0p ψ φ)

/-- Source-facing finite-Gaussian resummation estimate.  Compared with the
generic Cauchy theorem, the nested contour hypothesis and both probability
measure hypotheses have disappeared; only explicit physical weight estimates
and the final finite resummation budget remain. -/
theorem norm_balabanCMP116H_le_of_finiteGaussianPhysicalMajorants
    {d M N' nDelta nY lieDim : ℕ} [NeZero M] [NeZero N']
    {ιZ0' Ψ Φ E : Type*} [DecidableEq ιZ0'] [Norm E]
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
    (hbudget : ∀ Z,
      Finset.sum (cmp116HIndexFinset
        (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex
          (fun Z D P Z0 Z0p =>
            (gaussianData Z D P Z0 Z0p).toAnalyticData)
          (fun Z D P Z0 Z0p => cmp116Eq214FiniteGaussianBoundaryMajorant
            (outerBound Z D P Z0 Z0p) (innerBound Z D P Z0 Z0p)
            (interactionBound Z D P Z0 Z0p))) Z)
        (fun x => cmp116Eq214CauchyTermWeight
          (gaussianData Z x.1.1 x.1.2 x.2.1 x.2.2).toAnalyticData
          (cmp116Eq214FiniteGaussianBoundaryMajorant
            (outerBound Z x.1.1 x.1.2 x.2.1 x.2.2)
            (innerBound Z x.1.1 x.1.2 x.2.1 x.2.2)
            (interactionBound Z x.1.1 x.1.2 x.2.1 x.2.2))) ≤
        (hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight hp.blockScale hp.delta hp.kappa
            sourceMetric Z) :
    ∀ Z ψ φ,
      ‖balabanCMP116H
        (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex
          (fun Z D P Z0 Z0p =>
            (gaussianData Z D P Z0 Z0p).toAnalyticData)
          (fun Z D P Z0 Z0p => cmp116Eq214FiniteGaussianBoundaryMajorant
            (outerBound Z D P Z0 Z0p) (innerBound Z D P Z0 Z0p)
            (interactionBound Z D P Z0 Z0p))) Z ψ φ‖ ≤
        (hp.C3 * hp.epsilon1) *
          balabanCMP116Lemma3Weight hp.blockScale hp.delta hp.kappa
            sourceMetric Z := by
  apply norm_balabanCMP116H_le_termWeightSum hp
    (cmp116Eq214CauchyMajorizedResummation domainFamily allowed ambient
      distinguished Z0PrimeIndex
      (fun Z D P Z0 Z0p =>
        (gaussianData Z D P Z0 Z0p).toAnalyticData)
      (fun Z D P Z0 Z0p => cmp116Eq214FiniteGaussianBoundaryMajorant
        (outerBound Z D P Z0 Z0p) (innerBound Z D P Z0 Z0p)
        (interactionBound Z D P Z0 Z0p)))
    sourceMetric
  · exact cmp116Eq214CauchyMajorizedResummation_term_bound_of_finiteGaussianWeights
      domainFamily allowed ambient distinguished Z0PrimeIndex gaussianData
      outerBound innerBound interactionBound hDelta hY houter_nonneg houter
      hinner hinteraction
  · intro Z
    simpa using hbudget Z

end YangMills.RG
