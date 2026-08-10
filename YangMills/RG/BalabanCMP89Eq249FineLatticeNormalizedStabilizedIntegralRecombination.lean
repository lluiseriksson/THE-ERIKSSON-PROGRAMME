/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249FineLatticeNormalizedStabilizedEndpointIntegral

/-!
# PRE-VALIDATION: normalized physical fine-lattice endpoint recombination

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

The stabilized CMP89 integrand is literally the difference of two endpoint
terms.  This module constructs that split at physical spacing `(L^j)^(-1)`,
applies the sealed normalized contour theorem to each endpoint independently,
and recombines only after the two signed contour equalities have been proved.

The resulting bound retains the sum of the two physical `l1` weights.  A
separate theorem compares that sum using the exact unit-fine-edge cost
`exp (rho * (L^j)^(-1))`; the cost is not absorbed into an unnamed constant.

The physical bond-to-unit-edge producer, the Fourier/operator dictionary,
`B0`, window 15 and terminal fields remain open.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Physical fine-lattice scaling commutes exactly with addition of integer
displacements. -/
theorem cmp89Eq249PhysicalFineLatticeDisplacement_add
    {d : ℕ} (xi : ℝ) (u v : Fin d → ℤ) :
    cmp89Eq249PhysicalFineLatticeDisplacement xi
        (fun mu => u mu + v mu) =
      fun mu => cmp89Eq249PhysicalFineLatticeDisplacement xi u mu +
        cmp89Eq249PhysicalFineLatticeDisplacement xi v mu := by
  funext mu
  simp [cmp89Eq249PhysicalFineLatticeDisplacement]
  ring

/-- One physical endpoint after its own signed contour shift, with the exact
source normalization already applied. -/
def cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral
    (L j : ℕ) [NeZero L] (mass a rho : ℝ) (mu : Fin 4)
    (holderU endpointU : Fin 4 → ℤ) : ℂ :=
  cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
    cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
      (cmp89Eq251SignedContourMomentum rho
        (cmp89Eq251PhysicalBrillouinParameter x)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) endpointU)) mu
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) holderU)
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) endpointU)

/-- Named form of the independently signed normalized endpoint equality. -/
theorem cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_signedEndpoint
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU endpointU : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
        L j mass a mu holderU endpointU =
      cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral
        L j mass a rho mu holderU endpointU := by
  simpa [cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral] using
    (cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_signed
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass mu holderU endpointU)

/-- The literal source-normalized complete stabilized integral at physical
fine-lattice spacing and `alpha = 0`. -/
def cmp89Eq249NormalizedFineLatticeStabilizedIntegral
    (L j : ℕ) [NeZero L] (mass a : ℝ) (mu : Fin 4)
    (holderU transportU : Fin 4 → ℤ) : ℂ :=
  cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a 0
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) holderU)
      (cmp89Eq249PhysicalFineLatticeDisplacement
        (cmp89Eq249FineLatticeSpacing L j) transportU)

/-- The complete normalized physical integral is exactly the difference of
the two endpoint integrals shifted along their own signed contours.  Neither
endpoint equality is accepted as a hypothesis. -/
theorem cmp89Eq249NormalizedFineLatticeStabilizedIntegral_eq_sub_signedEndpoints
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU transportU : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFineLatticeStabilizedIntegral
        L j mass a mu holderU transportU =
      cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral
          L j mass a rho mu holderU
            (fun nu => holderU nu + transportU nu) -
        cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral
          L j mass a rho mu holderU transportU := by
  let firstU : Fin 4 → ℤ := fun nu => holderU nu + transportU nu
  let holderDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (cmp89Eq249FineLatticeSpacing L j) holderU
  let transportDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (cmp89Eq249FineLatticeSpacing L j) transportU
  let productMeasure : Measure (Fin 4 → ℝ) :=
    Measure.pi fun _ : Fin 4 => volume.restrict (Set.uIoc 0 (2 * Real.pi))
  have hfirstIntegrable : Integrable (fun x : Fin 4 → ℝ =>
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
        holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) firstU)) productMeasure := by
    simpa [productMeasure, holderDisplacement] using
      (integrable_cmp89Eq251ComplexStabilizedEndpointIntegrand_partialSigned
        (L := L) (j := j) (mass := mass) (a := a) (alpha := 0)
        (rho := rho)
        ha hmassPos hrho hamplitude hradius hwindow hmass
        0 mu holderDisplacement
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) firstU))
  have hsecondIntegrable : Integrable (fun x : Fin 4 → ℝ =>
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
        holderDisplacement transportDisplacement) productMeasure := by
    simpa [productMeasure, holderDisplacement, transportDisplacement] using
      (integrable_cmp89Eq251ComplexStabilizedEndpointIntegrand_partialSigned
        (L := L) (j := j) (mass := mass) (a := a) (alpha := 0)
        (rho := rho)
        ha hmassPos hrho hamplitude hradius hwindow hmass
        0 mu holderDisplacement transportDisplacement)
  have hadd :
      cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) firstU =
        fun nu => holderDisplacement nu + transportDisplacement nu := by
    simpa [firstU, holderDisplacement, transportDisplacement] using
      (cmp89Eq249PhysicalFineLatticeDisplacement_add
        (cmp89Eq249FineLatticeSpacing L j) holderU transportU)
  have hintegral :
      (∫ x, cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a 0
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
          holderDisplacement transportDisplacement ∂productMeasure) =
        (∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
          holderDisplacement
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) firstU) ∂productMeasure) -
        (∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
          holderDisplacement transportDisplacement ∂productMeasure) := by
    rw [← integral_sub hfirstIntegrable hsecondIntegrable]
    apply integral_congr_ae
    filter_upwards with x
    have hpoint :=
      cmp89Eq251ComplexStabilizedIntegrand_eq_sub_endpoint
        (L := L) (j := j) (mass := mass) (a := a) (alpha := 0)
        (z := fun nu =>
          (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        (mu := mu) holderDisplacement transportDisplacement
    rw [← hadd] at hpoint
    exact hpoint
  have hsplit :
      cmp89Eq249NormalizedFineLatticeStabilizedIntegral
          L j mass a mu holderU transportU =
        cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
            L j mass a mu holderU firstU -
          cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
            L j mass a mu holderU transportU := by
    unfold cmp89Eq249NormalizedFineLatticeStabilizedIntegral
      cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
      cmp89Eq249FourDimensionalBrillouinMeasure
    simp only [firstU, holderDisplacement, transportDisplacement] at hintegral ⊢
    rw [← mul_sub]
    exact congrArg
      (fun z : ℂ => ((((2 * Real.pi) ^ 4)⁻¹ : ℝ) : ℂ) * z) hintegral
  have hfirstShift :=
    cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_signedEndpoint
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass mu holderU firstU
  have hsecondShift :=
    cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_signedEndpoint
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass mu holderU transportU
  simpa [firstU] using
    hsplit.trans (congrArg₂ (fun x y : ℂ => x - y) hfirstShift hsecondShift)

/-- The complete normalized physical integral retains the sum of the two
independently shifted endpoint weights and the common explicit amplitude. -/
theorem norm_cmp89Eq249NormalizedFineLatticeStabilizedIntegral_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU transportU : Fin 4 → ℤ) :
    ‖cmp89Eq249NormalizedFineLatticeStabilizedIntegral
        L j mass a mu holderU transportU‖ ≤
      (Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (fun nu => holderU nu + transportU nu)))) +
        Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) transportU)))) *
        cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho := by
  rw [cmp89Eq249NormalizedFineLatticeStabilizedIntegral_eq_sub_signedEndpoints
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hmassPos hrho hamplitude hradius hwindow hmass]
  have hfirst :=
    norm_cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_le
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass mu holderU
        (fun nu => holderU nu + transportU nu)
  have hsecond :=
    norm_cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_le
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass mu holderU transportU
  rw [cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_signedEndpoint
    (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
    ha hmassPos hrho hamplitude hradius hwindow hmass] at hfirst hsecond
  calc
    ‖cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral
          L j mass a rho mu holderU (fun nu => holderU nu + transportU nu) -
        cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral
          L j mass a rho mu holderU transportU‖ ≤
        ‖cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral
          L j mass a rho mu holderU (fun nu => holderU nu + transportU nu)‖ +
        ‖cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral
          L j mass a rho mu holderU transportU‖ := norm_sub_le _ _
    _ ≤ Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (fun nu => holderU nu + transportU nu)))) *
          cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho +
        Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) transportU))) *
          cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho :=
      add_le_add hfirst hsecond
    _ = (Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (fun nu => holderU nu + transportU nu)))) +
        Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) transportU)))) *
          cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho :=
      by ring

/-- A unit fine edge compares the two endpoint weights with the exact visible
factor `exp (rho * (L^j)^(-1))`. -/
theorem cmp89Eq249PhysicalFineEndpointWeights_add_le
    {L j : ℕ} [NeZero L] {rho : ℝ} (hrho : 0 ≤ rho)
    {holder transport : Fin 4 → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holder) :
    Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j)
          (fun nu => holder nu + transport nu)))) +
      Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) transport))) ≤
      (1 + Real.exp (rho * cmp89Eq249FineLatticeSpacing L j)) *
        Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (fun nu => holder nu + transport nu)))) := by
  have htransport :=
    exp_neg_cmp89Eq251DisplacementL1_physicalFine_transport_le
      (L := L) (j := j) (holder := holder) (transport := transport)
      hrho hunit
  calc
    Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (fun nu => holder nu + transport nu)))) +
        Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j) transport))) ≤
        Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (fun nu => holder nu + transport nu)))) +
        Real.exp (rho * cmp89Eq249FineLatticeSpacing L j) *
          Real.exp (-(rho * cmp89Eq251DisplacementL1
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (cmp89Eq249FineLatticeSpacing L j)
              (fun nu => holder nu + transport nu)))) :=
      add_le_add le_rfl htransport
    _ = (1 + Real.exp (rho * cmp89Eq249FineLatticeSpacing L j)) *
        Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (cmp89Eq249FineLatticeSpacing L j)
            (fun nu => holder nu + transport nu)))) := by ring

end

end YangMills.RG
