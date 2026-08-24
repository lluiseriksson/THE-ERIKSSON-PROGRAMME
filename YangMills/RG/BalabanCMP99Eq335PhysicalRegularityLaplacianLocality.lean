import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityWitness
import YangMills.RG.BalabanCMP99SourceRetainedPhysicalPrecision

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# CMP99 (3.35): the exact Dirichlet-Laplacian read carrier

The zero-extended covariant derivative can be nonzero on a positive bond when
either endpoint belongs to the active region.  Therefore its background read
carrier is the one-bond collar, not merely the internal active bonds.

This module constructs that carrier and proves operator locality from literal
pointwise agreement there.  It also extends a cube-local gauge by the identity
only as a canonical implementation device and proves that, under the explicit
collar inclusion, the resulting regional Laplacian equals the one generated
by the physical exponential background.  No arbitrary operator equality is a
hypothesis.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Exact positive-bond read carrier of the zero-extended regional covariant
derivative: one endpoint in the active region is enough. -/
def cmp99ActiveRegionCovariantD0ReadBonds
    (Omega : ActiveGaugeRegion d N) : Finset (PhysicalBond d N) :=
  Finset.univ.filter fun b =>
    b.1 ∈ Omega.sites ∨ b.1.shift b.2 ∈ Omega.sites

@[simp] theorem mem_cmp99ActiveRegionCovariantD0ReadBonds_iff
    (Omega : ActiveGaugeRegion d N) (b : PhysicalBond d N) :
    b ∈ cmp99ActiveRegionCovariantD0ReadBonds Omega ↔
      b.1 ∈ Omega.sites ∨ b.1.shift b.2 ∈ Omega.sites := by
  simp [cmp99ActiveRegionCovariantD0ReadBonds]

/-- The regional covariant derivative reads the background only on its exact
one-bond collar. -/
theorem cmp99ActiveRegionSourceCovariantD0CLM_eq_of_eqOn_readBonds
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U V : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (hUV : ∀ b ∈ cmp99ActiveRegionCovariantD0ReadBonds Omega,
      U (positiveEdgeOfPhysicalBond b) =
        V (positiveEdgeOfPhysicalBond b)) :
    cmp99ActiveRegionSourceCovariantD0CLM Omega rho U spacing =
      cmp99ActiveRegionSourceCovariantD0CLM Omega rho V spacing := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro b
  change spacing⁻¹ •
      (extendZeroZeroCLM Omega phi b.1 -
        rho.adCLM (U (positiveEdgeOfPhysicalBond b))
          (extendZeroZeroCLM Omega phi (b.1.shift b.2))) =
    spacing⁻¹ •
      (extendZeroZeroCLM Omega phi b.1 -
        rho.adCLM (V (positiveEdgeOfPhysicalBond b))
          (extendZeroZeroCLM Omega phi (b.1.shift b.2)))
  by_cases hsource : b.1 ∈ Omega.sites
  · rw [hUV b (by simp [hsource])]
  · by_cases htarget : b.1.shift b.2 ∈ Omega.sites
    · rw [hUV b (by simp [htarget])]
    · rw [extendZeroZeroCLM_apply_of_not_mem Omega phi b.1 hsource,
        extendZeroZeroCLM_apply_of_not_mem Omega phi (b.1.shift b.2) htarget]
      simp

/-- The literal regional Dirichlet Laplacian inherits the same exact read
carrier theorem by construction as `D^* D`. -/
theorem cmp99ActiveRegionSourceCovariantLaplacian_eq_of_eqOn_readBonds
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U V : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (hUV : ∀ b ∈ cmp99ActiveRegionCovariantD0ReadBonds Omega,
      U (positiveEdgeOfPhysicalBond b) =
        V (positiveEdgeOfPhysicalBond b)) :
    cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing =
      cmp99ActiveRegionSourceCovariantLaplacian Omega rho V spacing := by
  have hD := cmp99ActiveRegionSourceCovariantD0CLM_eq_of_eqOn_readBonds
    Omega rho U V spacing hUV
  rw [cmp99ActiveRegionSourceCovariantLaplacian,
    cmp99ActiveRegionSourceCovariantLaplacian, hD]

section RegularCube

variable {L N' Mlarge n : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Mlarge]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}

/-- Canonical identity extension of a cube-local gauge.  No source statement
is asserted outside the cube. -/
def cmp99ExtendRegularCubeLocalGauge
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (u : {x // x ∈ C.carrier} → SUN Nc) :
    GaugeTransform 4 (L * N') (SUN Nc) :=
  fun x => if hx : x ∈ C.carrier then u ⟨x, hx⟩ else 1

@[simp] theorem cmp99ExtendRegularCubeLocalGauge_apply_of_mem
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (u : {x // x ∈ C.carrier} → SUN Nc)
    (x : FinBox 4 (L * N')) (hx : x ∈ C.carrier) :
    cmp99ExtendRegularCubeLocalGauge C u x = u ⟨x, hx⟩ := by
  unfold cmp99ExtendRegularCubeLocalGauge
  rw [dif_pos hx]

/-- On an interior positive bond, the global identity extension evaluates to
the literal local gauge action from the regularity witness. -/
theorem gaugeAct_cmp99ExtendRegularCubeLocalGauge_apply_interior
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (u : {x // x ∈ C.carrier} → SUN Nc)
    (b : CMP99SourceRegularCubeInteriorPositiveBond C) :
    GaugeConfig.gaugeAct (cmp99ExtendRegularCubeLocalGauge C u) U
        (positiveEdgeOfPhysicalBond b.1) =
      cmp99SourceLocalGaugeActPositiveBond C U u b := by
  rw [GaugeConfig.gaugeAct_apply]
  change cmp99ExtendRegularCubeLocalGauge C u b.1.1 *
      U (positiveEdgeOfPhysicalBond b.1) *
        (cmp99ExtendRegularCubeLocalGauge C u
          (b.1.1.shift b.1.2))⁻¹ =
    cmp99SourceLocalGaugeActPositiveBond C U u b
  rw [cmp99ExtendRegularCubeLocalGauge_apply_of_mem C u b.1.1 b.2.1,
    cmp99ExtendRegularCubeLocalGauge_apply_of_mem C u
      (b.1.1.shift b.1.2) b.2.2]
  rfl

/-- Canonical global exponential background associated with the physical
one-cochain extension. -/
noncomputable def cmp99Eq335PhysicalExponentialBackground
    (A : PhysicalGaugeOneCochain 4 (L * N') Nc) (eta : ℝ) :
    PhysicalGaugeBackground 4 (L * N') Nc :=
  gaugeConfigOfPositiveBonds fun b =>
    cmp98PhysicalSuIncrement (M := L) (N' := N') A b eta

/-- Explicit geometric gate saying the exact one-bond Laplacian collar lies
inside the regular cube. -/
def CMP99Eq335LaplacianReadCarrierInsideRegularCube
    (Omega : ActiveGaugeRegion 4 (L * N'))
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos) : Prop :=
  ∀ b ∈ cmp99ActiveRegionCovariantD0ReadBonds Omega,
    b.1 ∈ C.carrier ∧ b.1.shift b.2 ∈ C.carrier

/-- The witness's exponential identity supplies background equality on the
whole regional Laplacian read carrier once the geometric collar gate holds. -/
theorem CMP99Eq335PhysicalRegularityWitness.gaugeAct_eq_exponential_on_readBonds
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (S := S) (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1)
    (Omega : ActiveGaugeRegion 4 (L * N'))
    (hread : CMP99Eq335LaplacianReadCarrierInsideRegularCube
      (L := L) (N' := N') (Mlarge := Mlarge) (S := S)
      (scaleExtent_pos := scaleExtent_pos) Omega W.cube) :
    ∀ b ∈ cmp99ActiveRegionCovariantD0ReadBonds Omega,
      GaugeConfig.gaugeAct
          (cmp99ExtendRegularCubeLocalGauge W.cube W.localGauge) U
          (positiveEdgeOfPhysicalBond b) =
        cmp99Eq335PhysicalExponentialBackground
          W.logarithmicRepresentative eta
          (positiveEdgeOfPhysicalBond b) := by
  intro b hb
  let bi : CMP99SourceRegularCubeInteriorPositiveBond W.cube :=
    ⟨b, hread b hb⟩
  calc
    GaugeConfig.gaugeAct
          (cmp99ExtendRegularCubeLocalGauge W.cube W.localGauge) U
          (positiveEdgeOfPhysicalBond b) =
        cmp99SourceLocalGaugeActPositiveBond W.cube U W.localGauge bi := by
          exact gaugeAct_cmp99ExtendRegularCubeLocalGauge_apply_interior
            W.cube U W.localGauge bi
    _ = cmp98PhysicalSuIncrement (M := L) (N' := N')
          W.logarithmicRepresentative b eta := W.gauge_eq_exp_on_interior bi
    _ = cmp99Eq335PhysicalExponentialBackground
          W.logarithmicRepresentative eta
          (positiveEdgeOfPhysicalBond b) := by
          simp [cmp99Eq335PhysicalExponentialBackground]

/-- First f2 locality endpoint: the literal regional Laplacian built from the
canonically extended local gauge is exactly the one built from the source
exponential representative. -/
theorem CMP99Eq335PhysicalRegularityWitness.regionalLaplacian_eq_exponential
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 spacing : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (S := S) (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1)
    (Omega : ActiveGaugeRegion 4 (L * N'))
    (hread : CMP99Eq335LaplacianReadCarrierInsideRegularCube
      (L := L) (N' := N') (Mlarge := Mlarge) (S := S)
      (scaleExtent_pos := scaleExtent_pos) Omega W.cube) :
    cmp99ActiveRegionSourceCovariantLaplacian Omega
        (matrixSUNAdjointModel Nc)
        (GaugeConfig.gaugeAct
          (cmp99ExtendRegularCubeLocalGauge W.cube W.localGauge) U) spacing =
      cmp99ActiveRegionSourceCovariantLaplacian Omega
        (matrixSUNAdjointModel Nc)
        (cmp99Eq335PhysicalExponentialBackground
          W.logarithmicRepresentative eta) spacing := by
  exact cmp99ActiveRegionSourceCovariantLaplacian_eq_of_eqOn_readBonds
    Omega (matrixSUNAdjointModel Nc) _ _ spacing
    (W.gaugeAct_eq_exponential_on_readBonds Omega hread)

end RegularCube

end

end YangMills.RG
