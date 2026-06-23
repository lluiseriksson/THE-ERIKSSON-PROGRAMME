/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.MarginalUVMassGap
import YangMills.RG.PhysicalGaugeCMP116RawHsharp

/-!
# CMP116 raw-source H# input to the marginal M3 assembly

This file contains only source-independent endpoint plumbing.  It composes the
raw-source CMP116/H# `SingleScaleUVDecay` producer with the marginal-coupling
lattice mass-gap assembly.

No Gaussian pushforward, covariance-root localization, Wilson-Hessian
identification, physical local activity construction, raw pointwise estimate,
rooted H# remainder identity, H# profile estimate, marginal-flow estimate, or
IR estimate is proved here.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- The UV amplitude produced by the CMP116 raw-source H# endpoint. -/
noncomputable def cmp116RawHsharpUVAmplitude
    (d : ℕ) (C Hbar kappa0 : ℝ) : ℝ :=
  (C * Hbar) *
    (1 - ((3 ^ d : ℕ) : ℝ) ^ 2 *
      (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)))⁻¹

/-- Conditional M3 endpoint:
raw physical source → CMP116 → H# → single-scale UV decay →
marginal-coupling lattice mass-gap assembly.

Every physical/source estimate and the rooted remainder identity remain
explicit hypotheses. -/
theorem lattice_mass_gap_of_cmp116RawSource_hsharp_marginal
    {β : Type*} [MeasurableSpace β]
    {HF : HoleFamily d L}
    (zCarrier : Finset (Cube d L) → ℂ)
    (r : Cube d L)
    (z : ℕ → ℕ → Finset (Cube d L) → ℂ)
    (Λ : ∀ t k, Finset (OmegaPolymerType HF (z t k)))
    (D : ∀ _ _, PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (spectatorPull :
      ∀ _ _, ∀ _ : PhysicalBond dPhys N,
        β → SUNLieCoord Nc)
    (precision covariance root :
      ∀ _ _,
        PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
          PhysicalGaugeOneCochain dPhys N Nc)
    (physicalGaussian :
      ∀ _ _, Measure (PhysicalGaugeOneCochain dPhys N Nc))
    (covNormBound rootNormBound : ∀ _ _, ℝ)
    (covWeight rootWeight :
      ∀ _ _, PhysicalBond dPhys N → PhysicalBond dPhys N → ℝ)
    (physicalActivity :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          PhysicalGaugeLocalActivity dPhys N Nc)
    (physicalActiveSupport :
      ∀ t k,
        OmegaPolymerType HF (z t k) →
          Finset (PhysicalBond dPhys N))
    (weight :
      ∀ t k, OmegaPolymerType HF (z t k) → ℝ)
    (ν : ℕ → ℕ → Measure β)
    (covIR : ℕ → ℝ)
    (Rsc : ℕ → ℕ → ℝ)
    (nsc : ℕ → ℕ)
    (g : ℕ → ℝ)
    (amplitude : ℕ → ℕ → ℝ)
    {C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ}
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop)
    (hroot :
      ∀ t k,
        PhysicalLocalizedCovarianceRootCertificate
          (precision t k) (covariance t k) (root t k)
          (covNormBound t k) (rootNormBound t k)
          (covWeight t k) (rootWeight t k))
    (hsource :
      ∀ t k,
        PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
          (D t k) (root t k) (physicalGaussian t k)
          (physicalActivity t k) (weight t k) (amplitude t k)
          (rootLocalization t k)
          (wilsonHessianIdentification t k)
          (localActivityConstruction t k))
    (hspectator :
      ∀ t k X,
        (physicalActivity t k X).spectatorSupport ⊆
          physicalActiveSupport t k X)
    (hfluctuation :
      ∀ t k X,
        (physicalActivity t k X).fluctuationSupport ⊆
          physicalActiveSupport t k X)
    (hamplitude_nonneg : ∀ t k, 0 ≤ amplitude t k)
    (hamplitude_one : ∀ t k, amplitude t k ≤ 1)
    (hweight : ∀ t k X, 0 ≤ weight t k X)
    (activity_stronglyMeasurable :
      ∀ t k X, ∀ ψ : ∀ _ : Cube d L, β,
        StronglyMeasurable
          (fun ξ : CMP116FluctuationField d L lieDim =>
            ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
              (Ψ := fun _ : Cube d L => β)
              (D t k)
              (fun X : OmegaPolymerType HF (z t k) => X)
              (spectatorPull t k)).activity
                (physicalActivity t k) X).globalEval ψ ξ))
    (activeSupport_subset_Omega :
      ∀ t k X,
        physicalActiveSupport t k X ⊆
          (D t k).physicalBondsOfCells (D t k).siteMap.Omega)
    (activeSupport_subset_skeleton :
      ∀ t k X, X ∈ Λ t k →
        physicalActiveSupport t k X ⊆
          (D t k).physicalBondsOfCells (skeleton HF X.val))
    (weight_domination :
      ∀ t k X, X ∈ Λ t k →
        weight t k X ≤ appendixFHoleExpWeight HF kappa X.val)
    (hC : 0 ≤ C)
    (hHbar : 0 ≤ Hbar)
    (hkappa : 4 * kappa0 + 3 ≤ kappa)
    (hkappa0 : 1 < kappa0)
    (hpos : ∀ k, 0 < g k)
    (hR :
      ∀ t k,
        Rsc t k =
          ∑' P : { P : OmegaPolymerType HF zCarrier //
              r ∈ skeleton HF P.val },
            Complex.re
              (balabanCMP116AppendixFHsharpOfIntegratedKsharp
                HF (z t k) (Λ t k)
                ((physicalGaugeCMP116RawSourceScaleFamily
                  Λ D spectatorPull precision covariance
                  root physicalGaussian covNormBound rootNormBound covWeight
                  rootWeight physicalActivity physicalActiveSupport weight
                  amplitude kappa rootLocalization
                  wilsonHessianIdentification localActivityConstruction
                  hroot hsource hspectator hfluctuation hamplitude_nonneg
                  hweight activity_stronglyMeasurable
                  activeSupport_subset_Omega activeSupport_subset_skeleton
                  weight_domination) t k)
                (ν t k) P.val.val))
    (hν : ∀ t k, IsProbabilityMeasure (ν t k))
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H ∈ HF.holes, H.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1)
    (hhalf :
      ∀ t k,
        appendixFSecondUrsellLeafConstant d kappa0 *
            (2 * amplitude t k *
              appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2)
    (hprofile :
      ∀ t k,
        4 * appendixFSecondUrsellMomentConstant d kappa0 *
            amplitude t k * appendixFHoleRootSumConstant d kappa0 ≤
          C * Hbar * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0)
    (hε : 0 < ε)
    (hc0 : 0 < c0)
    (hbeta : 0 < betaFlow)
    (hsmall : ∀ k, betaFlow * g k < 1)
    (hrec :
      ∀ k, g (k + 1) = g k * (1 - betaFlow * g k))
    (hIRbound :
      ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ)))) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t| ≤
        (C1 + cmp116RawHsharpUVAmplitude d C Hbar kappa0 *
          (∑' k, g k ^ kappa0)) *
          Real.exp (-(gap * (t : ℝ))) := by
  have hA : 0 ≤ cmp116RawHsharpUVAmplitude d C Hbar kappa0 := by
    dsimp [cmp116RawHsharpUVAmplitude]
    exact mul_nonneg (mul_nonneg hC hHbar)
      (le_of_lt (inv_pos.mpr (sub_pos.mpr hCq)))
  have hUV :
      SingleScaleUVDecay Rsc g
        (cmp116RawHsharpUVAmplitude d C Hbar kappa0) c0 kappa0 := by
    simpa [cmp116RawHsharpUVAmplitude] using
      (singleScaleUVDecay_of_cmp116RawSource_hsharp
        (dPhys := dPhys) (N := N) (Nc := Nc)
        (d := d) (L := L) (lieDim := lieDim)
        (β := β) (HF := HF)
        (C := C) (Hbar := Hbar) (c0 := c0)
        (kappa := kappa) (kappa0 := kappa0)
        zCarrier r z Λ D spectatorPull precision covariance root
        physicalGaussian covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport weight ν Rsc g amplitude
        rootLocalization wilsonHessianIdentification
        localActivityConstruction
        hroot hsource hspectator hfluctuation
        hamplitude_nonneg hamplitude_one hweight
        activity_stronglyMeasurable activeSupport_subset_Omega
        activeSupport_subset_skeleton weight_domination
        hC hHbar
        (fun k => (hpos k).le)
        hkappa
        (lt_trans zero_lt_one hkappa0)
        hR hν hdisj hnoedges hholes_ne hCq hhalf hprofile)
  exact
    lattice_mass_gap_of_singleScaleUVDecay_marginal
      covIR Rsc nsc g
      hε hc0 hA hkappa0 hbeta hpos hsmall hrec hIRbound hUV

end YangMills.RG
