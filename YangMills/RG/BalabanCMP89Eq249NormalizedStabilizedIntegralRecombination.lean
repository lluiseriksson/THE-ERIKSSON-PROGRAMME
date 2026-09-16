/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249NormalizedStabilizedEndpointIntegralBound
import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointRecombination

/-!
# Normalized recombination of the two CMP89 endpoints

This module and its audit were compiler-verified in the cold run recorded in
the verification ledger.

The two endpoint contour shifts are already separate because their signed
contours need not agree.  This module applies the literal `(2*pi)^(-4)`
normalization to the complete stabilized integral, recombines the two
normalized endpoint integrals exactly, and retains the sum of their two
signed lattice `l1` weights.

It does not absorb the later one-link factor `exp rho`, transport to
localization owners, construct the complete physical `B0`, attain window 15,
discharge rows 23--24 or inhabit a `TermSource`.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The literal source-normalized complete stabilized integral in four
dimensions. -/
def cmp89Eq249NormalizedFourDimensionalStabilizedIntegral
    (L j : ℕ) [NeZero L] (mass a alpha : ℝ) (mu : Fin 4)
    (holderU transportU : Fin 4 → ℤ) : ℂ :=
  cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha
      (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
      (cmp89Eq251LatticeDisplacement holderU)
      (cmp89Eq251LatticeDisplacement transportU)

/-- Source normalization commutes exactly with the already sealed
endpoint-by-endpoint contour recombination. -/
theorem cmp89Eq249NormalizedFourDimensionalStabilizedIntegral_eq_sub_endpoints
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU transportU : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFourDimensionalStabilizedIntegral
        L j mass a alpha mu holderU transportU =
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => cmp89Eq251ComplexStabilizedEndpointIntegrand
          4 L j mass a alpha
          (cmp89Eq251SignedContourMomentum rho
            (cmp89Eq251PhysicalBrillouinParameter x)
            (cmp89Eq251LatticeDisplacement
              (fun nu ↦ holderU nu + transportU nu))) mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement
            (fun nu ↦ holderU nu + transportU nu))) -
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => cmp89Eq251ComplexStabilizedEndpointIntegrand
          4 L j mass a alpha
          (cmp89Eq251SignedContourMomentum rho
            (cmp89Eq251PhysicalBrillouinParameter x)
            (cmp89Eq251LatticeDisplacement transportU)) mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement transportU)) := by
  unfold cmp89Eq249NormalizedFourDimensionalStabilizedIntegral
  unfold cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
  unfold cmp89Eq249FourDimensionalBrillouinMeasure
  rw [integral_cmp89Eq251ComplexStabilizedIntegrand_eq_sub_signed_endpoints
    (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
    (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass mu
    holderU transportU]
  ring

/-- The complete normalized stabilized integral is bounded by the literal
sum of the two independently shifted endpoint weights times their common
explicit amplitude majorant. -/
theorem norm_cmp89Eq249NormalizedFourDimensionalStabilizedIntegral_le
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) {holderU transportU : Fin 4 → ℤ}
    (hholder : CMP89Eq251UnitLatticeBondDisplacement holderU) :
    ‖cmp89Eq249NormalizedFourDimensionalStabilizedIntegral
        L j mass a alpha mu holderU transportU‖ ≤
      (cmp89SignedLatticeL1ExponentialWeight rho
          (fun nu ↦ holderU nu + transportU nu) +
        cmp89SignedLatticeL1ExponentialWeight rho transportU) *
          cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho := by
  rw [cmp89Eq249NormalizedFourDimensionalStabilizedIntegral_eq_sub_endpoints
    (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
    (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass mu
    holderU transportU]
  have hfirst :=
    norm_cmp89Eq249NormalizedStabilizedEndpointIntegral_le
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hradius hmass hwindow hamplitude mu
      (endpointU := fun nu ↦ holderU nu + transportU nu) hholder
  have hsecond :=
    norm_cmp89Eq249NormalizedStabilizedEndpointIntegral_le
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hradius hmass hwindow hamplitude mu
      (endpointU := transportU) hholder
  calc
    ‖cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
          (fun x => cmp89Eq251ComplexStabilizedEndpointIntegrand
            4 L j mass a alpha
            (cmp89Eq251SignedContourMomentum rho
              (cmp89Eq251PhysicalBrillouinParameter x)
              (cmp89Eq251LatticeDisplacement
                (fun nu ↦ holderU nu + transportU nu))) mu
            (cmp89Eq251LatticeDisplacement holderU)
            (cmp89Eq251LatticeDisplacement
              (fun nu ↦ holderU nu + transportU nu))) -
        cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
          (fun x => cmp89Eq251ComplexStabilizedEndpointIntegrand
            4 L j mass a alpha
            (cmp89Eq251SignedContourMomentum rho
              (cmp89Eq251PhysicalBrillouinParameter x)
              (cmp89Eq251LatticeDisplacement transportU)) mu
            (cmp89Eq251LatticeDisplacement holderU)
            (cmp89Eq251LatticeDisplacement transportU))‖ ≤
        ‖cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
          (fun x => cmp89Eq251ComplexStabilizedEndpointIntegrand
            4 L j mass a alpha
            (cmp89Eq251SignedContourMomentum rho
              (cmp89Eq251PhysicalBrillouinParameter x)
              (cmp89Eq251LatticeDisplacement
                (fun nu ↦ holderU nu + transportU nu))) mu
            (cmp89Eq251LatticeDisplacement holderU)
            (cmp89Eq251LatticeDisplacement
              (fun nu ↦ holderU nu + transportU nu)))‖ +
        ‖cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
          (fun x => cmp89Eq251ComplexStabilizedEndpointIntegrand
            4 L j mass a alpha
            (cmp89Eq251SignedContourMomentum rho
              (cmp89Eq251PhysicalBrillouinParameter x)
              (cmp89Eq251LatticeDisplacement transportU)) mu
            (cmp89Eq251LatticeDisplacement holderU)
            (cmp89Eq251LatticeDisplacement transportU))‖ := norm_sub_le _ _
    _ ≤ cmp89SignedLatticeL1ExponentialWeight rho
          (fun nu ↦ holderU nu + transportU nu) *
            cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho +
        cmp89SignedLatticeL1ExponentialWeight rho transportU *
            cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho :=
      add_le_add hfirst hsecond
    _ = (cmp89SignedLatticeL1ExponentialWeight rho
          (fun nu ↦ holderU nu + transportU nu) +
        cmp89SignedLatticeL1ExponentialWeight rho transportU) *
          cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho := by ring

end

end YangMills.RG
