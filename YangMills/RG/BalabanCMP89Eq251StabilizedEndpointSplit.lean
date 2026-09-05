/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251ComplexContourPhase

/-!
# Endpoint split of the stabilized CMP89 integrand

Cold validation: exact source checkpoint
`e288842456b9a39e148eae4459620edb5abc5eb1` passed GitHub Actions run
`31292068036` with restore and save of `.lake/build` both skipped. The focal
completed 8,444 jobs and all six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

The Holder phase difference in CMP89 (2.49) has two physical endpoints:
`holder + transport` and `transport`.  They generally require different
signed contour directions.  This file constructs both endpoint integrands
from the literal stabilized alias formula and proves that their difference
is exactly the existing complete stabilized integrand.

This is an algebraic split only.  It does not shift the unsplit difference,
does not accept endpoint functions as input, and proves no endpoint
holomorphy, seam, bound `B0`, owner dictionary or window-15 conclusion.
-/

namespace YangMills.RG

noncomputable section

/-- One physical endpoint contribution to a bare reciprocal-alias numerator.
All non-phase factors are exactly those of the displayed CMP89 integrand. -/
def cmp89Eq251ComplexBareEndpointNumerator
    (d L j : ℕ) (alpha : ℝ) (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holderDisplacement endpointDisplacement : Fin d → ℝ) : ℂ :=
  let q := cmp89Eq248EntireAliasMomentum z m
  (Complex.exp (Complex.I *
        cmp89Eq251EntirePhase q endpointDisplacement) /
      ((cmp89Eq251EuclideanNorm holderDisplacement ^ alpha : ℝ) : ℂ)) *
    cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹) (-q mu) *
    cmp89Eq245EntireAverageAmplitude d (L ^ j) q

/-- The literal bare alias numerator is the difference of its two endpoint
numerators. -/
theorem cmp89Eq251ComplexBareAliasNumerator_eq_sub_endpoint
    {d L j : ℕ} {alpha : ℝ} (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holderDisplacement transportDisplacement : Fin d → ℝ) :
    cmp89Eq251ComplexBareAliasNumerator d L j alpha z m mu
        holderDisplacement transportDisplacement =
      cmp89Eq251ComplexBareEndpointNumerator d L j alpha z m mu
          holderDisplacement
          (fun nu => holderDisplacement nu + transportDisplacement nu) -
        cmp89Eq251ComplexBareEndpointNumerator d L j alpha z m mu
          holderDisplacement transportDisplacement := by
  rw [cmp89Eq251ComplexBareAliasNumerator_eq_phaseDifference]
  simp only [cmp89Eq251ComplexBareEndpointNumerator]
  ring

/-- The assembled stabilized numerator for one physical endpoint.  It keeps
the same zero-alias branch and noncentral fine-symbol quotients as the full
stabilized numerator. -/
def cmp89Eq251ComplexStabilizedEndpointNumerator
    (d L j : ℕ) (mass alpha : ℝ) (z : Fin d → ℂ) (mu : Fin d)
    (holderDisplacement endpointDisplacement : Fin d → ℝ) : ℂ :=
  cmp89Eq251ComplexBareEndpointNumerator d L j alpha z
      (cmp89Eq249ZeroAlias d) mu holderDisplacement endpointDisplacement +
    cmp89Eq249CentralEntireFineSymbol d L j mass z *
      ∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
          (cmp89Eq249ZeroAlias d),
        cmp89Eq251ComplexBareEndpointNumerator d L j alpha z m mu
            holderDisplacement endpointDisplacement /
          cmp89Eq245EntireScaledLaplacianSymbol d (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum z m)

/-- The complete stabilized numerator is the difference of the two assembled
endpoint numerators. -/
theorem cmp89Eq251ComplexStabilizedNumerator_eq_sub_endpoint
    {d L j : ℕ} {mass alpha : ℝ} (z : Fin d → ℂ) (mu : Fin d)
    (holderDisplacement transportDisplacement : Fin d → ℝ) :
    cmp89Eq251ComplexStabilizedNumerator d L j mass alpha z mu
        holderDisplacement transportDisplacement =
      cmp89Eq251ComplexStabilizedEndpointNumerator d L j mass alpha z mu
          holderDisplacement
          (fun nu => holderDisplacement nu + transportDisplacement nu) -
        cmp89Eq251ComplexStabilizedEndpointNumerator d L j mass alpha z mu
          holderDisplacement transportDisplacement := by
  unfold cmp89Eq251ComplexStabilizedNumerator
    cmp89Eq251ComplexStabilizedEndpointNumerator
  simp_rw [cmp89Eq251ComplexBareAliasNumerator_eq_sub_endpoint, sub_div,
    Finset.sum_sub_distrib]
  ring

/-- One endpoint contribution divided by the literal common stabilized
denominator. -/
def cmp89Eq251ComplexStabilizedEndpointIntegrand
    (d L j : ℕ) (mass a alpha : ℝ) (z : Fin d → ℂ) (mu : Fin d)
    (holderDisplacement endpointDisplacement : Fin d → ℝ) : ℂ :=
  cmp89Eq251ComplexStabilizedEndpointNumerator d L j mass alpha z mu
      holderDisplacement endpointDisplacement /
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a z

/-- The existing complete stabilized integrand is definitionally assembled
from, and exactly equal to, the difference of its two endpoint integrands. -/
theorem cmp89Eq251ComplexStabilizedIntegrand_eq_sub_endpoint
    {d L j : ℕ} {mass a alpha : ℝ} (z : Fin d → ℂ) (mu : Fin d)
    (holderDisplacement transportDisplacement : Fin d → ℝ) :
    cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha z mu
        holderDisplacement transportDisplacement =
      cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a alpha z mu
          holderDisplacement
          (fun nu => holderDisplacement nu + transportDisplacement nu) -
        cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a alpha z mu
          holderDisplacement transportDisplacement := by
  unfold cmp89Eq251ComplexStabilizedIntegrand
    cmp89Eq251ComplexStabilizedEndpointIntegrand
  rw [cmp89Eq251ComplexStabilizedNumerator_eq_sub_endpoint]
  ring

end

end YangMills.RG
