import YangMills.RG.BalabanCMP99Eq335PhysicalRegularityWitness

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# CMP99 (3.35): the all-admissible-cubes physical regularity class

Printed p. 396 defines the regularity class by requiring that, for an
arbitrary cube of the stated class, a cube-local gauge and logarithmic
representative exist with the two bounds in (3.35).  The later Corollary 3.6
then chooses one such cube containing `Omega'_0` and separately assumes
`O(1) M alpha0 <= alpha1`.

This module preserves that quantifier order.  It neither asserts regularity
for an arbitrary background nor stores the Corollary-3.6 scale gate in the
global class.  The old one-cube witness is derived only after a caller selects
the cube and supplies that literal scalar gate.
-/

namespace YangMills.RG

noncomputable section

variable {L N' Mlarge Nc n : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Mlarge] [NeZero Nc]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}
variable {scaleExtent_pos : ∀ r, 0 < scaleExtent r}

/-- The data furnished by (3.35) after one admissible cube has been fixed.
It contains no `alpha1` and no Corollary-3.6 scale gate. -/
structure CMP99Eq335PhysicalCubeRegularityData
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (eta alpha0 : ℝ) where
  localGauge : {x // x ∈ C.carrier} → SUN Nc
  logarithmicRepresentative : PhysicalGaugeOneCochain 4 (L * N') Nc
  gauge_eq_exp_on_interior :
    ∀ b : CMP99SourceRegularCubeInteriorPositiveBond C,
      cmp99SourceLocalGaugeActPositiveBond C U localGauge b =
        cmp98PhysicalSuIncrement (M := L) (N' := N')
          logarithmicRepresentative b.1 eta
  amplitude_bound :
    CMP99PhysicalOneCochainAmplitudeBoundOn C.carrier
      logarithmicRepresentative
      (cmp99Eq335PhysicalAmplitudeMajorant C eta alpha0)
  forward_derivative_bound :
    CMP99PhysicalForwardOneDerivativeBoundOn C.carrier eta
      logarithmicRepresentative
      (cmp99Eq335PhysicalForwardDerivativeMajorant C eta alpha0)

/-- Literal membership in the regularity class defined by CMP99 (3.35).
The existential choice is available for every admissible cube, not merely
for one cube hidden inside a record. -/
structure CMP99Eq335PhysicalRegularityClass
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (eta alpha0 : ℝ) : Prop where
  eta_pos : 0 < eta
  alpha0_pos : 0 < alpha0
  onCube :
    ∀ C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge
        scaleExtent S scaleExtent_pos,
      Nonempty (CMP99Eq335PhysicalCubeRegularityData C U eta alpha0)

/-- Specialize the all-cubes source premise to the cube selected in
Corollary 3.6 and add exactly its separate `O(1) M alpha0 <= alpha1` gate. -/
noncomputable def CMP99Eq335PhysicalRegularityClass.toCubeWitness
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {eta alpha0 : ℝ}
    (R : CMP99Eq335PhysicalRegularityClass
      (Mlarge := Mlarge) (S := S) (scaleExtent_pos := scaleExtent_pos)
      U eta alpha0)
    (C : CMP99SourceRegularCube (FinBox 4 (L * N')) n Mlarge scaleExtent S
      scaleExtent_pos)
    (alpha1 : ℝ)
    (hscale : (C.geometryFactor : ℝ) * (Mlarge : ℝ) * alpha0 ≤ alpha1) :
    CMP99Eq335PhysicalRegularityWitness
      (Mlarge := Mlarge) (S := S) (scaleExtent_pos := scaleExtent_pos)
      U eta alpha0 alpha1 := by
  let D := Classical.choice (R.onCube C)
  exact
    { cube := C
      localGauge := D.localGauge
      logarithmicRepresentative := D.logarithmicRepresentative
      eta_pos := R.eta_pos
      alpha0_pos := R.alpha0_pos
      gauge_eq_exp_on_interior := D.gauge_eq_exp_on_interior
      amplitude_bound := D.amplitude_bound
      forward_derivative_bound := D.forward_derivative_bound
      scale_gate := hscale }

end

end YangMills.RG
