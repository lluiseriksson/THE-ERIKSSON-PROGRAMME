import YangMills.RG.BalabanCMP99Eq335PhysicalLaplacianInternalCarrier
import YangMills.RG.BalabanCMP99Eq335SourceRegionDictionary

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.35): internal-bond Laplacian bridge for Corollary 3.6

The printed inclusion `Omega'_0 subset square` controls both endpoints of
every bond internal to the generated head region.  Boundary-crossing bonds do
not require source-background equality after forming `D^* D`; their gauge
action cancels from the quadratic form by adjoint isometry.  Thus this bridge
uses exactly the printed source-region dictionary and no exterior collar.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L N' Mlarge Nc n : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}

/-- The local regularity identity covers every internal bond of the source
region under the literal Corollary-3.6 inclusion. -/
theorem
    CMP99Eq335PhysicalRegularityWitness.transformedBackground_eq_exponential_on_internalBonds
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (D : CMP99Eq335Corollary36SourceRegionDictionary
      Omega OmegaPrime0 W.cube) :
    ∀ b ∈ Omega.bonds,
      W.transformedBackground (positiveEdgeOfPhysicalBond b) =
        cmp99Eq335PhysicalExponentialBackground
          W.logarithmicRepresentative eta
          (positiveEdgeOfPhysicalBond b) := by
  intro b hb
  have hendpoints :
      b.1 ∈ Omega.sites ∧ b.1.shift b.2 ∈ Omega.sites := by
    simpa [ActiveGaugeRegion.bonds] using hb
  have hsource : b.1 ∈ W.cube.carrier := by
    apply D.printed_omegaPrime0_subset_regularCube
    rw [← D.headRegion_eq_omegaPrime0]
    exact hendpoints.1
  have htarget : b.1.shift b.2 ∈ W.cube.carrier := by
    apply D.printed_omegaPrime0_subset_regularCube
    rw [← D.headRegion_eq_omegaPrime0]
    exact hendpoints.2
  let bi : CMP99SourceRegularCubeInteriorPositiveBond W.cube :=
    ⟨b, hsource, htarget⟩
  change GaugeConfig.gaugeAct
      (cmp99ExtendRegularCubeLocalGauge W.cube W.localGauge) U
        (positiveEdgeOfPhysicalBond b) = _
  calc
    GaugeConfig.gaugeAct
          (cmp99ExtendRegularCubeLocalGauge W.cube W.localGauge) U
          (positiveEdgeOfPhysicalBond b) =
        cmp99SourceLocalGaugeActPositiveBond
          W.cube U W.localGauge bi := by
      exact gaugeAct_cmp99ExtendRegularCubeLocalGauge_apply_interior
        W.cube U W.localGauge bi
    _ = cmp98PhysicalSuIncrement (M := L) (N' := N')
          W.logarithmicRepresentative b eta := W.gauge_eq_exp_on_interior bi
    _ = cmp99Eq335PhysicalExponentialBackground
          W.logarithmicRepresentative eta
          (positiveEdgeOfPhysicalBond b) := by
      simp [cmp99Eq335PhysicalExponentialBackground]

/-- The literal regional Laplacian of the transformed source background is
the exponential-background Laplacian under the printed source dictionary.
No one-bond exterior collar is assumed. -/
theorem
    CMP99Eq335PhysicalRegularityWitness.regionalLaplacian_eq_exponential_of_sourceRegionDictionary
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 spacing : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1)
    {Omega OmegaPrime0 : ActiveGaugeRegion 4 (L * N')}
    (D : CMP99Eq335Corollary36SourceRegionDictionary
      Omega OmegaPrime0 W.cube) :
    cmp99ActiveRegionSourceCovariantLaplacian Omega
        (matrixSUNAdjointModel Nc) W.transformedBackground spacing =
      cmp99ActiveRegionSourceCovariantLaplacian Omega
        (matrixSUNAdjointModel Nc)
        (cmp99Eq335PhysicalExponentialBackground
          W.logarithmicRepresentative eta) spacing := by
  exact cmp99ActiveRegionSourceCovariantLaplacian_eq_of_eqOn_internalBonds
    Omega (matrixSUNAdjointModel Nc) _ _ spacing
    (W.transformedBackground_eq_exponential_on_internalBonds D)

end

end YangMills.RG
