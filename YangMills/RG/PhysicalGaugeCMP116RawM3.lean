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

/-- Positivity of the CMP116 raw-H# UV amplitude.

This packages the denominator-smallness algebra used by the marginal M3
assembly, so downstream users no longer need to rebuild the local `hA` proof
each time they feed the UV endpoint into `lattice_mass_gap_of_singleScaleUVDecay_marginal`. -/
theorem cmp116RawHsharpUVAmplitude_nonneg
    {d : ℕ} {C Hbar kappa0 : ℝ}
    (hC : 0 ≤ C)
    (hHbar : 0 ≤ Hbar)
    (hsmall :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1) :
    0 ≤ cmp116RawHsharpUVAmplitude d C Hbar kappa0 := by
  dsimp [cmp116RawHsharpUVAmplitude]
  exact mul_nonneg (mul_nonneg hC hHbar)
    (le_of_lt (inv_pos.mpr (sub_pos.mpr hsmall)))

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
  have hA : 0 ≤ cmp116RawHsharpUVAmplitude d C Hbar kappa0 :=
    cmp116RawHsharpUVAmplitude_nonneg (d := d) hC hHbar hCq
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

/-- The remaining mathematical frontier between a scale-indexed physical
CMP116 raw source and the marginal M3 lattice assembly.

This record proves none of its fields.  It only separates the analytic-source,
support/geometric, measure-theoretic, and scale/marginal obligations already
consumed by `lattice_mass_gap_of_cmp116RawSource_hsharp_marginal`.

The truncation schedule `nsc` is deliberately not a parameter: no frontier
hypothesis constrains it. -/
structure CMP116RawSourceM3Frontier
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
    (g : ℕ → ℝ)
    (amplitude : ℕ → ℕ → ℝ)
    (C1 C Hbar ε c0 betaFlow kappa kappa0 : ℝ)
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop) : Prop where

  /- Analytic source facts. -/

  covariance_root_certificate :
    ∀ t k,
      PhysicalLocalizedCovarianceRootCertificate
        (precision t k) (covariance t k) (root t k)
        (covNormBound t k) (rootNormBound t k)
        (covWeight t k) (rootWeight t k)

  /-- Its projections are the Gaussian pushforward, root-localization,
  Wilson-Hessian identification, local-activity construction, and raw
  pointwise estimate. -/
  raw_source :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k) (root t k) (physicalGaussian t k)
        (physicalActivity t k) (weight t k) (amplitude t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k)

  /- Appendix-F support and geometric facts. -/

  spectator_support_subset :
    ∀ t k X,
      (physicalActivity t k X).spectatorSupport ⊆
        physicalActiveSupport t k X

  fluctuation_support_subset :
    ∀ t k X,
      (physicalActivity t k X).fluctuationSupport ⊆
        physicalActiveSupport t k X

  weight_nonneg :
    ∀ t k X, 0 ≤ weight t k X

  active_support_subset_omega :
    ∀ t k X,
      physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (D t k).siteMap.Omega

  active_support_subset_skeleton :
    ∀ t k X, X ∈ Λ t k →
      physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (skeleton HF X.val)

  weight_domination :
    ∀ t k X, X ∈ Λ t k →
      weight t k X ≤ appendixFHoleExpWeight HF kappa X.val

  holes_pairwise_disjoint :
    ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂

  no_edges_between_holes :
    noEdgesBetweenHoles (cubeAdj d L) HF.holes

  holes_nonempty :
    ∀ H ∈ HF.holes, H.Nonempty

  appendix_f_geometric_smallness :
    ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1

  /- Measure facts.

  Connected first-activity integrability is already derived by the existing
  source-measurable H# chain from factorwise strong measurability and the raw
  metric bound, so it is intentionally not duplicated as a stronger field. -/

  activity_stronglyMeasurable :
    ∀ t k X, ∀ ψ : ∀ _ : Cube d L, β,
      StronglyMeasurable
        (fun ξ : CMP116FluctuationField d L lieDim =>
          ((PhysicalGaugeCMP116ActivityAdapter.ofDictionary
            (Ψ := fun _ : Cube d L => β)
            (D t k)
            (fun X : OmegaPolymerType HF (z t k) => X)
            (spectatorPull t k)).activity
              (physicalActivity t k) X).globalEval ψ ξ)

  probability_law :
    ∀ t k, IsProbabilityMeasure (ν t k)

  /- Scale, Appendix-F budget, marginal flow, and IR facts. -/

  amplitude_nonneg :
    ∀ t k, 0 ≤ amplitude t k

  amplitude_le_one :
    ∀ t k, amplitude t k ≤ 1

  profile_constant_nonneg :
    0 ≤ C

  hbar_nonneg :
    0 ≤ Hbar

  kappa_margin :
    4 * kappa0 + 3 ≤ kappa

  kappa0_gt_one :
    1 < kappa0

  coupling_positive :
    ∀ k, 0 < g k

  half_budget :
    ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 * amplitude t k *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2

  profile_bound :
    ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          amplitude t k * appendixFHoleRootSumConstant d kappa0 ≤
        C * Hbar * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0

  epsilon_positive :
    0 < ε

  time_decay_positive :
    0 < c0

  beta_flow_positive :
    0 < betaFlow

  coupling_small :
    ∀ k, betaFlow * g k < 1

  coupling_recursion :
    ∀ k, g (k + 1) = g k * (1 - betaFlow * g k)

  ir_bound :
    ∀ k : ℕ,
      |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ)))

  /-- Physical identification of the scale remainder with the rooted real part
  of the integrated Appendix-F H# family.

  This field is placed last because its family depends definitionally on the
  analytic, support, positivity, and measurability fields above. -/
  rooted_hsharp_remainder_identity :
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
                covariance_root_certificate raw_source
                spectator_support_subset fluctuation_support_subset
                amplitude_nonneg weight_nonneg
                activity_stronglyMeasurable
                active_support_subset_omega
                active_support_subset_skeleton
                weight_domination) t k)
              (ν t k) P.val.val)

/-- A completed raw-source CMP116/H# frontier feeds the existing marginal
lattice M3 assembly. -/
theorem lattice_mass_gap_of_cmp116RawSourceM3Frontier
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
    (frontier :
      CMP116RawSourceM3Frontier
        (dPhys := dPhys) (N := N) (Nc := Nc)
        (d := d) (L := L) (lieDim := lieDim)
        (β := β) (HF := HF)
        zCarrier r z Λ D spectatorPull precision covariance root
        physicalGaussian covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport weight ν covIR Rsc g amplitude
        C1 C Hbar ε c0 betaFlow kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV_concrete Rsc nsc t| ≤
        (C1 + cmp116RawHsharpUVAmplitude d C Hbar kappa0 *
          (∑' k, g k ^ kappa0)) *
          Real.exp (-(gap * (t : ℝ))) := by
  exact
    lattice_mass_gap_of_cmp116RawSource_hsharp_marginal
      (dPhys := dPhys) (N := N) (Nc := Nc)
      (d := d) (L := L) (lieDim := lieDim)
      (β := β) (HF := HF)
      (C1 := C1) (C := C) (Hbar := Hbar)
      (ε := ε) (c0 := c0) (betaFlow := betaFlow)
      (kappa := kappa) (kappa0 := kappa0)
      zCarrier r z Λ D spectatorPull precision covariance root
      physicalGaussian covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport weight ν covIR Rsc nsc g
      amplitude rootLocalization wilsonHessianIdentification
      localActivityConstruction
      frontier.covariance_root_certificate
      frontier.raw_source
      frontier.spectator_support_subset
      frontier.fluctuation_support_subset
      frontier.amplitude_nonneg
      frontier.amplitude_le_one
      frontier.weight_nonneg
      frontier.activity_stronglyMeasurable
      frontier.active_support_subset_omega
      frontier.active_support_subset_skeleton
      frontier.weight_domination
      frontier.profile_constant_nonneg
      frontier.hbar_nonneg
      frontier.kappa_margin
      frontier.kappa0_gt_one
      frontier.coupling_positive
      frontier.rooted_hsharp_remainder_identity
      frontier.probability_law
      frontier.holes_pairwise_disjoint
      frontier.no_edges_between_holes
      frontier.holes_nonempty
      frontier.appendix_f_geometric_smallness
      frontier.half_budget
      frontier.profile_bound
      frontier.epsilon_positive
      frontier.time_decay_positive
      frontier.beta_flow_positive
      frontier.coupling_small
      frontier.coupling_recursion
      frontier.ir_bound

end YangMills.RG
