/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointProductContourTelescope
import YangMills.RG.BalabanCMP89SignedLatticeL1ExponentialSum

/-!
# PRE-VALIDATION: recombination of the two stabilized CMP89 endpoints

The source is present, but its `.olean` has not yet been materialized and the
result has not yet been verified by the compiler.

The literal stabilized integrand is the difference of two endpoint terms.
Each endpoint has already been transported along its own signed four-coordinate
contour.  This file recombines those two equalities without imposing a common
contour.

The later localized bound also needs to compare the two endpoint decays.  The
comparison below exposes its exact lattice input: the Holder displacement must
be one unit edge in `l1`.  Under that named condition, the second endpoint costs
the literal factor `exp rho` relative to the first.  No owner-to-bond dictionary
is assumed or constructed here, and the factor is not absorbed into `B0`.

This is infrastructure below window 15.  It does not construct the complete
strip bound `B0`, identify physical owners with integer displacements, attain
window 15, discharge rows 23--24, or inhabit a `TermSource`.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The literal `l1` length of an integer lattice displacement, in lattice
edge units. -/
def cmp89Eq251LatticeL1Length {d : ℕ} (u : Fin d → ℤ) : ℝ :=
  ∑ mu, ((u mu).natAbs : ℝ)

/-- A displacement is one literal unit-lattice edge.  The future physical
owner dictionary must construct this condition from its bond data. -/
def CMP89Eq251UnitLatticeBondDisplacement {d : ℕ}
    (u : Fin d → ℤ) : Prop :=
  cmp89Eq251LatticeL1Length u = 1

/-- Coordinatewise addition satisfies the literal lattice `l1` triangle
inequality. -/
theorem cmp89Eq251LatticeL1Length_add_le {d : ℕ}
    (u v : Fin d → ℤ) :
    cmp89Eq251LatticeL1Length (fun mu ↦ u mu + v mu) ≤
      cmp89Eq251LatticeL1Length u + cmp89Eq251LatticeL1Length v := by
  unfold cmp89Eq251LatticeL1Length
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun mu _ ↦ by
    exact_mod_cast Int.natAbs_add_le (u mu) (v mu)

/-- The endpoint `holder + transport` is at `l1` distance at most one more
than `transport` when the Holder displacement is one lattice edge. -/
theorem cmp89Eq251LatticeL1Length_add_le_add_one_of_unit {d : ℕ}
    {holder transport : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holder) :
    cmp89Eq251LatticeL1Length (fun mu ↦ holder mu + transport mu) ≤
      cmp89Eq251LatticeL1Length transport + 1 := by
  have hunit' : cmp89Eq251LatticeL1Length holder = 1 := by
    simpa [CMP89Eq251UnitLatticeBondDisplacement] using hunit
  have h := cmp89Eq251LatticeL1Length_add_le holder transport
  calc
    cmp89Eq251LatticeL1Length (fun mu ↦ holder mu + transport mu) ≤
        cmp89Eq251LatticeL1Length holder +
          cmp89Eq251LatticeL1Length transport := h
    _ = cmp89Eq251LatticeL1Length transport + 1 := by
      rw [hunit']
      ring

/-- Explicit neighbour cost for the two endpoint decays.  This is the exact
`exp rho` factor that must remain visible when the physical endpoint bounds
are recombined. -/
theorem cmp89SignedLatticeL1ExponentialWeight_transport_le_exp_mul_add
    {d : ℕ} {rho : ℝ} (hrho : 0 ≤ rho)
    {holder transport : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holder) :
    cmp89SignedLatticeL1ExponentialWeight rho transport ≤
      Real.exp rho *
        cmp89SignedLatticeL1ExponentialWeight rho
          (fun mu ↦ holder mu + transport mu) := by
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
    cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  have hlength :=
    cmp89Eq251LatticeL1Length_add_le_add_one_of_unit
      (holder := holder) (transport := transport) hunit
  have hexponent :
      -rho * cmp89Eq251LatticeL1Length transport ≤
        rho + -rho *
          cmp89Eq251LatticeL1Length
            (fun mu ↦ holder mu + transport mu) := by
    have hmul := mul_le_mul_of_nonneg_left hlength hrho
    nlinarith
  calc
    Real.exp (-rho * ∑ mu, ((transport mu).natAbs : ℝ)) ≤
        Real.exp (rho + -rho *
          ∑ mu, (((holder mu + transport mu).natAbs : ℕ) : ℝ)) := by
      simpa [cmp89Eq251LatticeL1Length] using
        (Real.exp_le_exp.mpr hexponent)
    _ = Real.exp rho *
        Real.exp (-rho *
          ∑ mu, (((holder mu + transport mu).natAbs : ℕ) : ℝ)) := by
      rw [Real.exp_add]

/-- The complete real stabilized product integral is exactly the difference
of the two endpoint integrals transported along their own signed contours.
The first endpoint is `holder + transport`; the second is `transport`.
No shared contour and no endpoint bound are accepted as hypotheses. -/
theorem integral_cmp89Eq251ComplexStabilizedIntegrand_eq_sub_signed_endpoints
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU transportU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
        (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU)
      ∂(Measure.pi fun _ : Fin 4 ↦
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      (∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand
        4 L j mass a alpha
        (cmp89Eq251SignedContourMomentum rho
          (cmp89Eq251PhysicalBrillouinParameter x)
          (cmp89Eq251LatticeDisplacement
            (fun nu ↦ holderU nu + transportU nu))) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement
          (fun nu ↦ holderU nu + transportU nu))
        ∂(Measure.pi fun _ : Fin 4 ↦
          volume.restrict (Set.uIoc 0 (2 * Real.pi)))) -
      (∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand
        4 L j mass a alpha
        (cmp89Eq251SignedContourMomentum rho
          (cmp89Eq251PhysicalBrillouinParameter x)
          (cmp89Eq251LatticeDisplacement transportU)) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU)
        ∂(Measure.pi fun _ : Fin 4 ↦
          volume.restrict (Set.uIoc 0 (2 * Real.pi)))) := by
  let endpointU : Fin 4 → ℤ := fun nu ↦ holderU nu + transportU nu
  let productMeasure : Measure (Fin 4 → ℝ) :=
    Measure.pi fun _ : Fin 4 ↦ volume.restrict (Set.uIoc 0 (2 * Real.pi))
  have hfirstIntegrable : Integrable (fun x : Fin 4 → ℝ ↦
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
        (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU)) productMeasure := by
    simpa [productMeasure] using
      (integrable_cmp89Eq251ComplexStabilizedEndpointIntegrand_partialSigned
        (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
        (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
        0 mu (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU))
  have hsecondIntegrable : Integrable (fun x : Fin 4 → ℝ ↦
      cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
        (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU)) productMeasure := by
    simpa [productMeasure] using
      (integrable_cmp89Eq251ComplexStabilizedEndpointIntegrand_partialSigned
        (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
        (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
        0 mu (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement transportU))
  have hsplit :
      (∫ x, cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
          (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement transportU) ∂productMeasure) =
        (∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand
            4 L j mass a alpha
            (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
            (cmp89Eq251LatticeDisplacement holderU)
            (cmp89Eq251LatticeDisplacement endpointU) ∂productMeasure) -
          (∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand
            4 L j mass a alpha
            (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
            (cmp89Eq251LatticeDisplacement holderU)
            (cmp89Eq251LatticeDisplacement transportU) ∂productMeasure) := by
    rw [← integral_sub hfirstIntegrable hsecondIntegrable]
    apply integral_congr_ae
    filter_upwards with x
    simpa [endpointU, cmp89Eq251LatticeDisplacement] using
      (cmp89Eq251ComplexStabilizedIntegrand_eq_sub_endpoint
        (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
        (z := fun nu ↦
          (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        (mu := mu)
        (holderDisplacement := cmp89Eq251LatticeDisplacement holderU)
        (transportDisplacement := cmp89Eq251LatticeDisplacement transportU))
  have hfirst :=
    integral_cmp89Eq251ComplexStabilizedEndpointIntegrand_eq_signed
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
      mu holderU endpointU
  have hsecond :=
    integral_cmp89Eq251ComplexStabilizedEndpointIntegrand_eq_signed
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
      mu holderU transportU
  simpa [endpointU, productMeasure] using
    hsplit.trans (congrArg₂ (fun x y : ℂ ↦ x - y) hfirst hsecond)

end

end YangMills.RG
