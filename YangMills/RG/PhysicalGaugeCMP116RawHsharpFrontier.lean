/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeCMP116RawM3

/-!
# Auditable frontier for the raw-source CMP116/H# endpoint

This file is intentionally a bookkeeping layer.  It gives the long hypothesis
surface of the raw-source CMP116/H# endpoint a single auditable name and then
projects that bundle into the already verified UV and marginal-M3 consumers.

No Gaussian pushforward, covariance-root localization, Wilson-Hessian
identification, local activity construction, rooted H# identity, H# profile
estimate, marginal-flow estimate, or IR estimate is proved here.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- The exact hypothesis frontier for the raw-source CMP116/H# UV endpoint.

The three source propositions are kept as explicit fields because the current
physical source API still exposes them as source facts.  This record does not
solve or weaken them; it only names the complete boundary that must eventually
be discharged by the physical Hessian/root/local-activity construction. -/
structure PhysicalGaugeCMP116RawHsharpFrontier
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
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (amplitude : ℕ → ℕ → ℝ)
    (C Hbar c0 kappa kappa0 : ℝ)
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop) : Prop where
  hroot :
    ∀ t k,
      PhysicalLocalizedCovarianceRootCertificate
        (precision t k) (covariance t k) (root t k)
        (covNormBound t k) (rootNormBound t k)
        (covWeight t k) (rootWeight t k)
  hsource :
    ∀ t k,
      PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
        (D t k) (root t k) (physicalGaussian t k)
        (physicalActivity t k) (weight t k) (amplitude t k)
        (rootLocalization t k)
        (wilsonHessianIdentification t k)
        (localActivityConstruction t k)
  hspectator :
    ∀ t k X,
      (physicalActivity t k X).spectatorSupport ⊆
        physicalActiveSupport t k X
  hfluctuation :
    ∀ t k X,
      (physicalActivity t k X).fluctuationSupport ⊆
        physicalActiveSupport t k X
  hamplitude_nonneg : ∀ t k, 0 ≤ amplitude t k
  hamplitude_one : ∀ t k, amplitude t k ≤ 1
  hweight : ∀ t k X, 0 ≤ weight t k X
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
  activeSupport_subset_Omega :
    ∀ t k X,
      physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (D t k).siteMap.Omega
  activeSupport_subset_skeleton :
    ∀ t k X, X ∈ Λ t k →
      physicalActiveSupport t k X ⊆
        (D t k).physicalBondsOfCells (skeleton HF X.val)
  weight_domination :
    ∀ t k X, X ∈ Λ t k →
      weight t k X ≤ appendixFHoleExpWeight HF kappa X.val
  hC : 0 ≤ C
  hHbar : 0 ≤ Hbar
  hg : ∀ k, 0 ≤ g k
  hkappa : 4 * kappa0 + 3 ≤ kappa
  hkappa0 : 0 < kappa0
  hR :
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
              (ν t k) P.val.val)
  hν : ∀ t k, IsProbabilityMeasure (ν t k)
  hdisj :
    ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
      H₁ ≠ H₂ → Disjoint H₁ H₂
  hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes
  hholes_ne : ∀ H ∈ HF.holes, H.Nonempty
  hCq :
    ((3 ^ d : ℕ) : ℝ) ^ 2 *
        (Real.exp (-kappa0) * 2 ^ (3 ^ d + 1)) < 1
  hhalf :
    ∀ t k,
      appendixFSecondUrsellLeafConstant d kappa0 *
          (2 * amplitude t k *
            appendixFHoleRootSumConstant d kappa0) ≤ 1 / 2
  hprofile :
    ∀ t k,
      4 * appendixFSecondUrsellMomentConstant d kappa0 *
          amplitude t k * appendixFHoleRootSumConstant d kappa0 ≤
        C * Hbar * Real.exp (-(c0 * (t : ℝ))) * g k ^ kappa0

/-- Projection of the named frontier into the raw-source CMP116/H# UV endpoint. -/
theorem PhysicalGaugeCMP116RawHsharpFrontier.singleScaleUVDecay
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
    (Rsc : ℕ → ℕ → ℝ)
    (g : ℕ → ℝ)
    (amplitude : ℕ → ℕ → ℝ)
    {C Hbar c0 kappa kappa0 : ℝ}
    (rootLocalization
      wilsonHessianIdentification
      localActivityConstruction : ℕ → ℕ → Prop)
    (frontier :
      PhysicalGaugeCMP116RawHsharpFrontier
        (dPhys := dPhys) (N := N) (Nc := Nc)
        (d := d) (L := L) (lieDim := lieDim)
        zCarrier r z Λ D spectatorPull precision covariance root
        physicalGaussian covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport weight ν Rsc g amplitude
        C Hbar c0 kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction) :
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
      rootLocalization wilsonHessianIdentification localActivityConstruction
      frontier.hroot frontier.hsource frontier.hspectator
      frontier.hfluctuation frontier.hamplitude_nonneg
      frontier.hamplitude_one frontier.hweight
      frontier.activity_stronglyMeasurable
      frontier.activeSupport_subset_Omega
      frontier.activeSupport_subset_skeleton frontier.weight_domination
      frontier.hC frontier.hHbar frontier.hg frontier.hkappa
      frontier.hkappa0 frontier.hR frontier.hν frontier.hdisj
      frontier.hnoedges frontier.hholes_ne frontier.hCq frontier.hhalf
      frontier.hprofile)

/-- Projection of the named frontier into the marginal-coupling lattice M3
assembly.  The marginal-flow and IR hypotheses remain separate because they are
consumer-side inputs, not raw-source/H# source obligations. -/
theorem PhysicalGaugeCMP116RawHsharpFrontier.lattice_mass_gap_marginal
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
      PhysicalGaugeCMP116RawHsharpFrontier
        (dPhys := dPhys) (N := N) (Nc := Nc)
        (d := d) (L := L) (lieDim := lieDim)
        zCarrier r z Λ D spectatorPull precision covariance root
        physicalGaussian covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport weight ν Rsc g amplitude
        C Hbar c0 kappa kappa0
        rootLocalization wilsonHessianIdentification
        localActivityConstruction)
    (hε : 0 < ε)
    (hc0 : 0 < c0)
    (hkappa0_marginal : 1 < kappa0)
    (hbeta : 0 < betaFlow)
    (hpos : ∀ k, 0 < g k)
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
    exact mul_nonneg (mul_nonneg frontier.hC frontier.hHbar)
      (le_of_lt (inv_pos.mpr (sub_pos.mpr frontier.hCq)))
  have hUV :
      SingleScaleUVDecay Rsc g
        (cmp116RawHsharpUVAmplitude d C Hbar kappa0) c0 kappa0 :=
    frontier.singleScaleUVDecay
      (dPhys := dPhys) (N := N) (Nc := Nc)
      (d := d) (L := L) (lieDim := lieDim)
      zCarrier r z Λ D spectatorPull precision covariance root
      physicalGaussian covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport weight ν Rsc g amplitude
      rootLocalization wilsonHessianIdentification
      localActivityConstruction
  exact
    lattice_mass_gap_of_singleScaleUVDecay_marginal
      covIR Rsc nsc g
      hε hc0 hA hkappa0_marginal hbeta hpos hsmall hrec hIRbound hUV

/-- The full raw-source M3 frontier canonically contains the narrower raw-H#
frontier.

This is a pure projection theorem.  It proves no source, Gaussian, H#, flow, or
IR estimate.  It only records that the M3 frontier's analytic/geometric/measure
fields already include exactly the source-independent inputs consumed by the
raw-H# UV endpoint. -/
theorem CMP116RawSourceM3Frontier.toRawHsharpFrontier
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
    PhysicalGaugeCMP116RawHsharpFrontier
      (dPhys := dPhys) (N := N) (Nc := Nc)
      (d := d) (L := L) (lieDim := lieDim)
      zCarrier r z Λ D spectatorPull precision covariance root
      physicalGaussian covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport weight ν Rsc g amplitude
      C Hbar c0 kappa kappa0
      rootLocalization wilsonHessianIdentification
      localActivityConstruction where
  hroot := frontier.covariance_root_certificate
  hsource := frontier.raw_source
  hspectator := frontier.spectator_support_subset
  hfluctuation := frontier.fluctuation_support_subset
  hamplitude_nonneg := frontier.amplitude_nonneg
  hamplitude_one := frontier.amplitude_le_one
  hweight := frontier.weight_nonneg
  activity_stronglyMeasurable := frontier.activity_stronglyMeasurable
  activeSupport_subset_Omega := frontier.active_support_subset_omega
  activeSupport_subset_skeleton := frontier.active_support_subset_skeleton
  weight_domination := frontier.weight_domination
  hC := frontier.profile_constant_nonneg
  hHbar := frontier.hbar_nonneg
  hg := fun k => (frontier.coupling_positive k).le
  hkappa := frontier.kappa_margin
  hkappa0 := lt_trans zero_lt_one frontier.kappa0_gt_one
  hR := frontier.rooted_hsharp_remainder_identity
  hν := frontier.probability_law
  hdisj := frontier.holes_pairwise_disjoint
  hnoedges := frontier.no_edges_between_holes
  hholes_ne := frontier.holes_nonempty
  hCq := frontier.appendix_f_geometric_smallness
  hhalf := frontier.half_budget
  hprofile := frontier.profile_bound

/-- Projection of a completed raw-source M3 frontier to the raw-H#
`SingleScaleUVDecay` endpoint.

This exposes the UV part of the M3 frontier without requiring callers to
reconstruct the narrower `PhysicalGaugeCMP116RawHsharpFrontier` by hand. -/
theorem CMP116RawSourceM3Frontier.singleScaleUVDecay
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
    SingleScaleUVDecay Rsc g
      (cmp116RawHsharpUVAmplitude d C Hbar kappa0) c0 kappa0 := by
  exact
    (CMP116RawSourceM3Frontier.toRawHsharpFrontier
      (dPhys := dPhys) (N := N) (Nc := Nc)
      (d := d) (L := L) (lieDim := lieDim)
      (β := β) (HF := HF)
      (C1 := C1) (ε := ε) (betaFlow := betaFlow)
      zCarrier r z Λ D spectatorPull precision covariance root
      physicalGaussian covNormBound rootNormBound covWeight rootWeight
      physicalActivity physicalActiveSupport weight ν covIR Rsc g amplitude
      rootLocalization wilsonHessianIdentification
      localActivityConstruction frontier).singleScaleUVDecay
        (dPhys := dPhys) (N := N) (Nc := Nc)
        (d := d) (L := L) (lieDim := lieDim)
        zCarrier r z Λ D spectatorPull precision covariance root
        physicalGaussian covNormBound rootNormBound covWeight rootWeight
        physicalActivity physicalActiveSupport weight ν Rsc g amplitude
        rootLocalization wilsonHessianIdentification
        localActivityConstruction

end YangMills.RG
