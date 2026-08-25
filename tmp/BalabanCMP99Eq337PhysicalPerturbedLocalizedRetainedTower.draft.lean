import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTower
import YangMills.RG.BalabanCMP99Eq337PhysicalRealGaugeCovariance
import YangMills.RG.BalabanCMP99Eq337PhysicalRealPerturbedNearIdentity

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.37): retained tower of the physical real perturbation

This module constructs the retained tower for the literal background
`exp(eta A') U` in the same gauge representative and on the same regional
chain as the regular baseline tower.  The transformed (3.37) domain and the
retained-read smallness premise are derived internally.  No `Q1`, `F2`,
precision, Green operator or operator identity is accepted from the caller.

It is the physical real slice only.  The analytically continued complex tower
and the independently constructed printed starred coefficient remain open.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {L N' M Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero N'] [NeZero M] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r ⇒ FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}

/-- The two adjacent printed strata supporting a regular cube are both
contained in the earlier source region `Omega_j`.  This is the missing
geometric direction needed to consume the literal (3.37) bound. -/
theorem CMP99SourceRegularCube.carrier_subset_globalRegion
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos) :
    C.carrier ⊆ S.global.regions C.scaleIndex.castSucc := by
  intro x hx
  have hadjacent := C.carrier_subset_adjacent_strata hx
  rcases Finset.mem_union.mp hadjacent with hhere | hnext
  · rw [cmp99SourceExtendedFineStratum_castSucc] at hhere
    exact S.global.stratum_subset_region C.scaleIndex hhere
  · by_cases hs : C.scaleIndex.val + 1 < n
    · let r : Fin n := ⟨C.scaleIndex.val + 1, hs⟩
      have hr : x ∈ S.global.stratum r := by
        simpa [cmp99SourceExtendedFineStratum, hs, r] using hnext
      have hrRegion : x ∈ S.global.regions r.castSucc :=
        S.global.stratum_subset_region r hr
      apply S.global.regions_subset_of_le _ hrRegion
      change C.scaleIndex.val ≤ r.val
      simp [r]
    · simpa [cmp99SourceExtendedFineStratum, hs, S.global.final_empty]
        using hnext

/-- Radius obtained by multiplying a background of radius `2 alpha1` by the
literal (3.37) perturbation, whose exponential increment also costs
`2 alpha1`.  The two contributions stay visible in the proof below. -/
def cmp99Eq337PhysicalPerturbedRetainedNearIdentityRadius
    (alpha1 : ℝ) : ℝ :=
  4 * alpha1

/-- The (3.37) domain, its gauge transport and the printed cube geometry
produce the retained-read smallness premise for the literal perturbed
background. -/
theorem CMP99Eq335PhysicalRegularityClass.norm_localizedPhysicalPerturbedBackground_sub_one_le
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 spacing : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (Dsource : CMP99Eq335Corollary36SourceRegionDictionary
      Omega OmegaPrime0 C)
    (A : PhysicalGaugeOneCochain 4 (L * N') Nc)
    (Dpert : CMP99Eq337PhysicalRealPerturbationDomain
      (S := S) U A eta alpha1)
    (halpha1 : alpha1 ≤ 1 / 2) :
    let W := R.toCubeWitness C alpha1 hscale
    let u := cmp99ExtendRegularCubeLocalGauge W.cube W.localGauge
    let A1 := cmp99Eq337PhysicalGaugeTransformRealOneCochain u A
    ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(cmp98PhysicalSuLeftVariation W.transformedBackground A1 eta
          (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99Eq337PhysicalPerturbedRetainedNearIdentityRadius alpha1 := by
  dsimp only
  intro q hq
  let W := R.toCubeWitness C alpha1 hscale
  let u := cmp99ExtendRegularCubeLocalGauge W.cube W.localGauge
  let A1 := cmp99Eq337PhysicalGaugeTransformRealOneCochain u A
  have hinside :=
    CMP99Eq335Corollary36SourceRegionDictionary.
      retainedFineReadCarrierInsideRegularCube C Dsource regions
  have hqRegion : q.1 ∈ S.global.regions C.scaleIndex.castSucc :=
    C.carrier_subset_globalRegion (hinside q hq).1
  have Dtransported : CMP99Eq337PhysicalRealPerturbationDomain (S := S)
      W.transformedBackground A1 eta alpha1 := by
    simpa [W, u, A1,
      CMP99Eq335PhysicalRegularityWitness.transformedBackground] using
      Dpert.gaugeAct u
  have hbaseline :
      ‖(W.transformedBackground (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1 :=
    W.retainedFineReadBonds_nearIdentity regions hinside halpha1 q hq
  have hproduct :=
    norm_cmp98PhysicalSuLeftVariation_apply_pos_sub_one_le_of_eq337
      (S := S) W.transformedBackground A1 eta alpha1
      (cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1)
      Dtransported C.scaleIndex q hqRegion halpha1 hbaseline
  calc
    ‖(cmp98PhysicalSuLeftVariation W.transformedBackground A1 eta
          (positiveEdgeOfPhysicalBond q) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        2 * (|eta| *
          cmp99Eq337PhysicalAmplitudeMajorant
            L C.scaleIndex.val eta alpha1) +
          cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1 := hproduct
    _ ≤ 4 * alpha1 := by
      have hamp :=
        Dtransported.abs_eta_mul_amplitudeMajorant_le C.scaleIndex
      unfold cmp99Eq335PhysicalRetainedNearIdentityRadius
      linarith
    _ = cmp99Eq337PhysicalPerturbedRetainedNearIdentityRadius alpha1 := rfl

/-- Source-specific real tower for the multiplicatively perturbed background.
The background, transported perturbation and local-smallness proof are all
constructed inside the definition. -/
noncomputable def
    CMP99Eq335PhysicalRegularityClass.localizedPerturbedRetainedTowerOfSourceRegion
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 spacing : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (Dsource : CMP99Eq335Corollary36SourceRegionDictionary
      Omega OmegaPrime0 C)
    (hM : 2 ≤ M)
    (A : PhysicalGaugeOneCochain 4 (L * N') Nc)
    (Dpert : CMP99Eq337PhysicalRealPerturbationDomain
      (S := S) U A eta alpha1)
    (halpha1 : alpha1 ≤ 1 / 2)
    (chain : CMP99SourceUbarRadiusChain 4 M Nc depth
      (cmp99Eq337PhysicalPerturbedRetainedNearIdentityRadius alpha1)) :
    let W := R.toCubeWitness C alpha1 hscale
    let u := cmp99ExtendRegularCubeLocalGauge W.cube W.localGauge
    let A1 := cmp99Eq337PhysicalGaugeTransformRealOneCochain u A
    CMP99SourceLocalizedRetainedTower regions (by norm_num : 2 ≤ 4) hM
      (matrixSUNAdjointModel Nc) spacing
      (cmp99Eq337PhysicalPerturbedRetainedNearIdentityRadius alpha1)
      (cmp98PhysicalSuLeftVariation W.transformedBackground A1 eta) chain
      (R.norm_localizedPhysicalPerturbedBackground_sub_one_le
        C hscale regions Dsource A Dpert halpha1) := by
  let W := R.toCubeWitness C alpha1 hscale
  let u := cmp99ExtendRegularCubeLocalGauge W.cube W.localGauge
  let A1 := cmp99Eq337PhysicalGaugeTransformRealOneCochain u A
  exact cmp99SourceLocalizedRetainedTower regions (by norm_num : 2 ≤ 4) hM
    (matrixSUNAdjointModel Nc) spacing
    (cmp99Eq337PhysicalPerturbedRetainedNearIdentityRadius alpha1)
    (cmp98PhysicalSuLeftVariation W.transformedBackground A1 eta) chain
    (R.norm_localizedPhysicalPerturbedBackground_sub_one_le
      C hscale regions Dsource A Dpert halpha1)

end

end YangMills.RG
