import YangMills.RG.BalabanCMP98PhysicalSpecialUnitaryChart
import YangMills.RG.BalabanCMP99Eq335PhysicalForwardDerivative
import YangMills.RG.BalabanCMP99SourceRegularCube

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# CMP99 (3.35): local physical regularity witness

The gauge furnished by CMP99 is local to one regular cube.  Accordingly this
interface does not extend it to a global `GaugeTransform`, and it does not
claim a global identity between `gaugeAct u U` and an exponential field.

The logarithmic representative uses the existing global physical one-cochain
coordinate only as an extension device required by the physical `SU(N)` chart.
Every law below reads it on the cube.  A later locality theorem must prove that
regional operators are independent of its values outside the protected read
carrier before this witness can feed the generated tower.
-/

namespace YangMills.RG

noncomputable section

variable {L N' Mlarge Nc n : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}

/-- Positive physical bonds whose source and target both lie in the printed
regular cube.  This is the exact domain on which a cube-local gauge can act
without an arbitrary exterior extension. -/
abbrev CMP99SourceRegularCubeInteriorPositiveBond
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos) :=
  {b : PhysicalBond 4 (L * N') //
    b.1 ∈ C.carrier ∧ b.1.shift b.2 ∈ C.carrier}

/-- Local positive-bond gauge action.  Both evaluations of `u` are justified
by the proof carried by the interior-bond subtype. -/
def cmp99SourceLocalGaugeActPositiveBond
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (u : {x // x ∈ C.carrier} → SUN Nc)
    (b : CMP99SourceRegularCubeInteriorPositiveBond C) : SUN Nc :=
  u ⟨b.1.1, b.2.1⟩ * U (positiveEdgeOfPhysicalBond b.1) *
    (u ⟨b.1.1.shift b.1.2, b.2.2⟩)⁻¹

@[simp] theorem cmp99SourceLocalGaugeActPositiveBond_apply
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (u : {x // x ∈ C.carrier} → SUN Nc)
    (b : CMP99SourceRegularCubeInteriorPositiveBond C) :
    cmp99SourceLocalGaugeActPositiveBond C U u b =
      u ⟨b.1.1, b.2.1⟩ * U (positiveEdgeOfPhysicalBond b.1) *
        (u ⟨b.1.1.shift b.1.2, b.2.2⟩)⁻¹ := by
  rfl

/-- The physical spacing of a scale-`j` regular cube in (3.35). -/
def cmp99Eq335PhysicalScaleSpacing
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (eta : ℝ) : ℝ :=
  (L : ℝ) ^ C.scaleIndex.val * eta

/-- Literal first majorant in (3.35). -/
def cmp99Eq335PhysicalAmplitudeMajorant
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (eta alpha0 : ℝ) : ℝ :=
  (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 *
    (cmp99Eq335PhysicalScaleSpacing C eta)⁻¹

/-- Literal derivative majorant in (3.35). -/
def cmp99Eq335PhysicalForwardDerivativeMajorant
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (eta alpha0 : ℝ) : ℝ :=
  (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 *
    ((cmp99Eq335PhysicalScaleSpacing C eta)⁻¹) ^ 2

/-- Source-facing local witness for CMP99 (3.35).

`U^u = exp(i eta A)` is represented only on positive bonds whose two endpoints
belong to the same regular cube.  The two analytic bounds use the literal
ordinary forward derivative `nabla^eta A`; no background-covariant derivative
or plaquette curl appears in the contract. -/
structure CMP99Eq335PhysicalRegularityWitness
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (eta alpha0 alpha1 : ℝ) where
  cube : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
    scaleExtent_pos
  localGauge : {x // x ∈ cube.carrier} → SUN Nc
  logarithmicRepresentative : PhysicalGaugeOneCochain 4 (L * N') Nc
  eta_pos : 0 < eta
  alpha0_pos : 0 < alpha0
  gauge_eq_exp_on_interior :
    ∀ b : CMP99SourceRegularCubeInteriorPositiveBond cube,
      cmp99SourceLocalGaugeActPositiveBond cube U localGauge b =
        cmp98PhysicalSuIncrement (M := L) (N' := N')
          logarithmicRepresentative b.1 eta
  amplitude_bound :
    CMP99PhysicalOneCochainAmplitudeBoundOn cube.carrier
      logarithmicRepresentative
      (cmp99Eq335PhysicalAmplitudeMajorant cube eta alpha0)
  forward_derivative_bound :
    CMP99PhysicalForwardOneDerivativeBoundOn cube.carrier eta
      logarithmicRepresentative
      (cmp99Eq335PhysicalForwardDerivativeMajorant cube eta alpha0)
  scale_gate :
    (cube.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1

end

end YangMills.RG
