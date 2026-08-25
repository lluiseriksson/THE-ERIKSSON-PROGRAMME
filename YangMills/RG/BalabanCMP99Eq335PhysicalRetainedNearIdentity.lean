import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityLaplacianLocality
import YangMills.RG.BalabanCMP99SourceLocalizedRetainedTower
import YangMills.RG.BalabanCMP116WilsonPlaquetteEnergy
import YangMills.RG.OrderedExponentialQuadraticBound

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# CMP99 (3.35): retained near-identity links from the exponential chart

The source regularity witness gives `U^u = exp(eta A)` only inside one regular
cube.  The retained source tower reads a finite, recursively generated family
of positive bonds.  This module keeps the required geometric inclusion visible
and derives the exact local smallness premise consumed by the retained tower.

The existing exponential estimate gives the conservative radius `2 * alpha1`.
No global smallness of the original or transformed background is asserted.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {L N' M Mlarge Nc n depth : ℕ}
variable [NeZero L] [NeZero N'] [NeZero M] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}
variable {Omega : ActiveGaugeRegion 4 (L * N')}

local instance cmp99Eq335RetainedNearIdentityMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Geometric gate required by (3.35): every positive bond read by the retained
tower has both endpoints inside the regular cube on which the local gauge and
its exponential representative are identified. -/
def CMP99Eq335RetainedFineReadCarrierInsideRegularCube
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos) : Prop :=
  ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
    q.1 ∈ C.carrier ∧ q.1.shift q.2 ∈ C.carrier

/-- Radius delivered by the repository's half-unit exponential estimate. -/
def cmp99Eq335PhysicalRetainedNearIdentityRadius (alpha1 : ℝ) : ℝ :=
  2 * alpha1

/-- The literal gauge-transformed background selected by the source witness.
Naming it prevents later consumers from choosing an unrelated small field. -/
def CMP99Eq335PhysicalRegularityWitness.transformedBackground
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1) :
    PhysicalGaugeBackground 4 (L * N') Nc :=
  GaugeConfig.gaugeAct
    (cmp99ExtendRegularCubeLocalGauge W.cube W.localGauge) U

/-- The fine spacing in (3.35) cancels internally.  Thus the printed scalar
gate controls the exponential argument uniformly at every scale index. -/
theorem CMP99Eq335PhysicalRegularityWitness.abs_eta_mul_amplitudeMajorant_le
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1) :
    |eta| * cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0 ≤ alpha1 := by
  have hL : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (NeZero.one_le : 1 ≤ L)
  have hpow : (1 : ℝ) ≤ (L : ℝ) ^ W.cube.scaleIndex.val :=
    one_le_pow₀ hL
  have hinv : ((L : ℝ) ^ W.cube.scaleIndex.val)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hpow
  have hcoefficient : 0 ≤
      (W.cube.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      W.alpha0_pos.le
  have hcancel :
      |eta| * cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0 =
        ((W.cube.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0) *
          ((L : ℝ) ^ W.cube.scaleIndex.val)⁻¹ := by
    rw [abs_of_pos W.eta_pos]
    unfold cmp99Eq335PhysicalAmplitudeMajorant
      cmp99Eq335PhysicalScaleSpacing
    field_simp [W.eta_pos.ne']
    <;> ring
  calc
    |eta| * cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0 =
        ((W.cube.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0) *
          ((L : ℝ) ^ W.cube.scaleIndex.val)⁻¹ := hcancel
    _ ≤ ((W.cube.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0) * 1 :=
      mul_le_mul_of_nonneg_left hinv hcoefficient
    _ = (W.cube.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 := by ring
    _ ≤ alpha1 := W.scale_gate

/-- The local exponential identity and the literal amplitude bound produce
the exact retained-link premise used by the localized tower.  The only extra
inputs are the source-geometric carrier inclusion and the half-unit scalar
window required by the already audited exponential lemma. -/
theorem CMP99Eq335PhysicalRegularityWitness.retainedFineReadBonds_nearIdentity
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 alpha1 : ℝ}
    (W : CMP99Eq335PhysicalRegularityWitness
      (L := L) (N' := N') (Mlarge := Mlarge) (Nc := Nc) (n := n)
      (scaleExtent := scaleExtent) (S := S)
      (scaleExtent_pos := scaleExtent_pos) U eta alpha0 alpha1)
    (regions : CMP99SourceActiveRegionChain 4 M (L * N') Omega depth)
    (hinside : CMP99Eq335RetainedFineReadCarrierInsideRegularCube
      (Nc := Nc) regions W.cube)
    (halpha1 : alpha1 ≤ 1 / 2) :
    ∀ q ∈ regions.retainedFineReadBonds (Nc := Nc),
      ‖(W.transformedBackground (positiveEdgeOfPhysicalBond q) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
        cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1 := by
  intro q hq
  let qi : CMP99SourceRegularCubeInteriorPositiveBond W.cube :=
    ⟨q, hinside q hq⟩
  let X : SuLie Nc :=
    (suLieCoordIso Nc).symm (W.logarithmicRepresentative q)
  have hX : ‖X.toMatrix‖ ≤
      cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0 := by
    calc
      ‖X.toMatrix‖ ≤ ‖X‖ := norm_suLie_toMatrix_l2_opNorm_le X
      _ = ‖W.logarithmicRepresentative q‖ := by
        exact (suLieCoordIso Nc).symm.norm_map _
      _ ≤ cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0 :=
        (W.amplitude_bound q.1 (hinside q hq).1 q.2).le
  have hscaled := W.abs_eta_mul_amplitudeMajorant_le
  have hsmall : |eta| *
      cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0 ≤ 1 / 2 :=
    hscaled.trans halpha1
  have hexp := norm_exp_smul_sub_one_le_two_mul eta
    (cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0)
    X.toMatrix hX hsmall
  have hbackground :
      (W.transformedBackground (positiveEdgeOfPhysicalBond q) :
            Matrix (Fin Nc) (Fin Nc) ℂ) =
        physicalMatrixExp (eta • X.toMatrix) := by
    unfold CMP99Eq335PhysicalRegularityWitness.transformedBackground
    rw [gaugeAct_cmp99ExtendRegularCubeLocalGauge_apply_interior
      W.cube U W.localGauge qi]
    rw [W.gauge_eq_exp_on_interior qi]
    rfl
  rw [hbackground]
  calc
    ‖physicalMatrixExp (eta • X.toMatrix) - 1‖ ≤
        2 * (|eta| *
          cmp99Eq335PhysicalAmplitudeMajorant W.cube eta alpha0) := by
      simpa only [physicalMatrixExp] using hexp
    _ ≤ 2 * alpha1 := by gcongr
    _ = cmp99Eq335PhysicalRetainedNearIdentityRadius alpha1 := rfl

end

end YangMills.RG
