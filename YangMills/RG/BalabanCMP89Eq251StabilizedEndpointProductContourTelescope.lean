/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointProductCoordinateShift

/-!
# PRE-VALIDATION: four-coordinate telescope for one stabilized endpoint

The source in this module is present, but its `.olean` has not yet been
materialized and its result has not yet been verified by the Lean compiler.

The sealed product-coordinate transition is composed at the four literal
coordinates of `Fin 4`.  Each intermediate momentum has all earlier
coordinates shifted inside the same full polydisc, so no one-coordinate-only
nonvanishing premise is introduced.  The endpoint theorem then rewrites stage
zero to the physical Brillouin momentum and stage four to the endpoint-specific
signed momentum.

This module treats one endpoint only.  It does not recombine the two endpoint
terms, compare their lattice displacements, construct `B0`, install the owner
dictionary or attain window 15.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The four literal coordinate transitions telescope from the real product
integral at stage zero to the fully signed product integral at stage four. -/
theorem integral_cmp89Eq251StabilizedEndpointPartialProductIntegrand_zero_eq_four
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU endpointU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq251StabilizedEndpointPartialProductIntegrand
        L j mass a alpha rho 0 mu holderU endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq251StabilizedEndpointPartialProductIntegrand
        L j mass a alpha rho 4 mu holderU endpointU x
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have h0 :=
    integral_cmp89Eq251StabilizedEndpointPartialProductIntegrand_stage_succ
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
      (stage := 0) (nu := (0 : Fin 4)) (mu := mu) (hstage := by norm_num)
      (holderU := holderU) (endpointU := endpointU)
  have h1 :=
    integral_cmp89Eq251StabilizedEndpointPartialProductIntegrand_stage_succ
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
      (stage := 1) (nu := (1 : Fin 4)) (mu := mu) (hstage := by norm_num)
      (holderU := holderU) (endpointU := endpointU)
  have h2 :=
    integral_cmp89Eq251StabilizedEndpointPartialProductIntegrand_stage_succ
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
      (stage := 2) (nu := (2 : Fin 4)) (mu := mu) (hstage := by norm_num)
      (holderU := holderU) (endpointU := endpointU)
  have h3 :=
    integral_cmp89Eq251StabilizedEndpointPartialProductIntegrand_stage_succ
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
      (stage := 3) (nu := (3 : Fin 4)) (mu := mu) (hstage := by norm_num)
      (holderU := holderU) (endpointU := endpointU)
  exact h0.trans (h1.trans (h2.trans h3))

/-- One physical stabilized endpoint product integral equals its own fully
signed contour integral.  No common sign is imposed on a second endpoint. -/
theorem integral_cmp89Eq251ComplexStabilizedEndpointIntegrand_eq_signed
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU endpointU : Fin 4 → ℤ) :
    (∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
        (fun nu =>
          (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU)
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi)))) =
      ∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
        (cmp89Eq251SignedContourMomentum rho
          (cmp89Eq251PhysicalBrillouinParameter x)
          (cmp89Eq251LatticeDisplacement endpointU)) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU)
      ∂(Measure.pi fun _ : Fin 4 =>
        volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
  have h :=
    integral_cmp89Eq251StabilizedEndpointPartialProductIntegrand_zero_eq_four
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass mu
      holderU endpointU
  simpa [cmp89Eq251StabilizedEndpointPartialProductIntegrand] using h

end

end YangMills.RG
