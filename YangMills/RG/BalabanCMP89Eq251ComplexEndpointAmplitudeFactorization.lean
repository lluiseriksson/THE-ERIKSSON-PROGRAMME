/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251ComplexNoncentralEndpointQuotientSum
import YangMills.RG.BalabanCMP89Eq251LatticePhasePeriodicity
import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointSplit

/-!
# PRE-VALIDATION: exact endpoint-amplitude factorization below CMP89 (2.49)

Source is present, its `.olean` has not yet been materialized, and the results
have not yet been verified by the compiler.

For a literal lattice endpoint, every reciprocal alias changes the Fourier
phase by an integral multiple of `2*pi`.  This file proves that equality for
an arbitrary alias vector, factors the common phase out of the noncentral
sum, and rewrites the complete stabilized endpoint numerator as

`common lattice phase * (central amplitude + central fine symbol *
  noncentral quotient sum)`.

The factorization is exact.  It does not bound the central amplitude or the
complete bracket, construct `B0`, transport to localization owners, attain
window 15 or discharge a terminal field.
-/

namespace YangMills.RG

noncomputable section

/-- Integer pairing that measures the phase acquired by a reciprocal alias
against a lattice endpoint. -/
def cmp89Eq251AliasLatticePairing {d : ℕ}
    (m u : Fin d → ℤ) : ℤ :=
  ∑ mu, m mu * u mu

/-- An arbitrary reciprocal alias changes a lattice-endpoint phase by the
explicit integral multiple `2*pi*<m,u>`. -/
theorem cmp89Eq251EntireAliasPhase_eq_add_latticePairing
    {d : ℕ} (z : Fin d → ℂ) (m u : Fin d → ℤ) :
    cmp89Eq251EntirePhase (cmp89Eq248EntireAliasMomentum z m)
        (cmp89Eq251LatticeDisplacement u) =
      cmp89Eq251EntirePhase z (cmp89Eq251LatticeDisplacement u) +
        ((2 * Real.pi * cmp89Eq251AliasLatticePairing m u : ℝ) : ℂ) := by
  rw [cmp89Eq251EntirePhase, cmp89Eq251EntirePhase,
    cmp89Eq248EntireAliasMomentum, Finset.sum_add_distrib]
  congr 1
  rw [cmp89Eq251AliasLatticePairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  simp only [cmp89Eq245AliasShift, cmp89Eq251LatticeDisplacement]
  push_cast
  ring

/-- Every reciprocal alias has exactly the zero-alias endpoint phase on a
literal lattice displacement. -/
theorem exp_I_cmp89Eq251EntireAliasPhase_eq_unshifted
    {d : ℕ} (z : Fin d → ℂ) (m u : Fin d → ℤ) :
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum z m)
        (cmp89Eq251LatticeDisplacement u)) =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase z
        (cmp89Eq251LatticeDisplacement u)) := by
  rw [cmp89Eq251EntireAliasPhase_eq_add_latticePairing, mul_add,
    Complex.exp_add]
  have hcycle :
      Complex.exp (Complex.I *
          ((2 * Real.pi * cmp89Eq251AliasLatticePairing m u : ℝ) : ℂ)) = 1 := by
    rw [show
      Complex.I *
          ((2 * Real.pi * cmp89Eq251AliasLatticePairing m u : ℝ) : ℂ) =
        ((cmp89Eq251AliasLatticePairing m u : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I
      (cmp89Eq251AliasLatticePairing m u)
  rw [hcycle, mul_one]

/-- Common phase and Holder normalization carried by every alias of one
lattice endpoint. -/
def cmp89Eq251ComplexEndpointLatticePhaseFactor
    {d : ℕ} (alpha : ℝ) (z : Fin d → ℂ)
    (holderU endpointU : Fin d → ℤ) : ℂ :=
  Complex.exp (Complex.I * cmp89Eq251EntirePhase z
      (cmp89Eq251LatticeDisplacement endpointU)) /
    ((cmp89Eq251EuclideanNorm
        (cmp89Eq251LatticeDisplacement holderU) ^ alpha : ℝ) : ℂ)

/-- The phase-free central endpoint amplitude. -/
def cmp89Eq251ComplexCentralEndpointAmplitude
    (L j : ℕ) (z : Fin 4 → ℂ) (mu : Fin 4) : ℂ :=
  cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹) (-z mu) *
    cmp89Eq245EntireAverageAmplitude 4 (L ^ j) z

/-- Complete phase-free bracket of one stabilized endpoint numerator. -/
def cmp89Eq251ComplexEndpointAmplitude
    (L j : ℕ) (mass : ℝ) (z : Fin 4 → ℂ) (mu : Fin 4) : ℂ :=
  cmp89Eq251ComplexCentralEndpointAmplitude L j z mu +
    cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
      cmp89Eq251ComplexNoncentralEndpointQuotientSum L j mass z mu

/-- One noncentral endpoint branch is the common lattice phase times the
phase-free quotient used by the sealed alias sum. -/
theorem cmp89Eq251ComplexBareEndpoint_div_fine_eq_phaseFactor_mul_quotient
    {L j : ℕ} {mass alpha : ℝ} (z : Fin 4 → ℂ)
    (m : Fin 4 → ℤ) (mu : Fin 4)
    (holderU endpointU : Fin 4 → ℤ) :
    cmp89Eq251ComplexBareEndpointNumerator 4 L j alpha z m mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement endpointU) /
        cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
          (cmp89Eq248EntireAliasMomentum z m) =
      cmp89Eq251ComplexEndpointLatticePhaseFactor alpha z holderU endpointU *
        (cmp89Eq245EntireScaledDifference (((L : ℝ) ^ j)⁻¹)
              (-(cmp89Eq248EntireAliasMomentum z m mu)) *
            cmp89Eq245EntireAverageAmplitude 4 (L ^ j)
              (cmp89Eq248EntireAliasMomentum z m) /
            cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
              (cmp89Eq248EntireAliasMomentum z m)) := by
  unfold cmp89Eq251ComplexBareEndpointNumerator
    cmp89Eq251ComplexEndpointLatticePhaseFactor
  rw [exp_I_cmp89Eq251EntireAliasPhase_eq_unshifted]
  ring

/-- The whole noncentral endpoint sum factors through the exact common
lattice phase. -/
theorem cmp89Eq251ComplexBareEndpoint_noncentralSum_eq_phaseFactor_mul_sum
    {L j : ℕ} {mass alpha : ℝ} (z : Fin 4 → ℂ) (mu : Fin 4)
    (holderU endpointU : Fin 4 → ℤ) :
    (∑ m ∈ (cmp89Eq245CenteredAliasVectors 4 (L ^ j)).erase
        (cmp89Eq249ZeroAlias 4),
      cmp89Eq251ComplexBareEndpointNumerator 4 L j alpha z m mu
            (cmp89Eq251LatticeDisplacement holderU)
            (cmp89Eq251LatticeDisplacement endpointU) /
          cmp89Eq245EntireScaledLaplacianSymbol 4 (((L : ℝ) ^ j)⁻¹) mass
            (cmp89Eq248EntireAliasMomentum z m)) =
      cmp89Eq251ComplexEndpointLatticePhaseFactor alpha z holderU endpointU *
        cmp89Eq251ComplexNoncentralEndpointQuotientSum L j mass z mu := by
  rw [cmp89Eq251ComplexNoncentralEndpointQuotientSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact cmp89Eq251ComplexBareEndpoint_div_fine_eq_phaseFactor_mul_quotient
    z m mu holderU endpointU

/-- The zero-alias endpoint branch carries the same common lattice phase. -/
theorem cmp89Eq251ComplexBareEndpoint_zero_eq_phaseFactor_mul_centralAmplitude
    {L j : ℕ} {alpha : ℝ} (z : Fin 4 → ℂ) (mu : Fin 4)
    (holderU endpointU : Fin 4 → ℤ) :
    cmp89Eq251ComplexBareEndpointNumerator 4 L j alpha z
          (cmp89Eq249ZeroAlias 4) mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq251ComplexEndpointLatticePhaseFactor alpha z holderU endpointU *
        cmp89Eq251ComplexCentralEndpointAmplitude L j z mu := by
  unfold cmp89Eq251ComplexBareEndpointNumerator
    cmp89Eq251ComplexEndpointLatticePhaseFactor
    cmp89Eq251ComplexCentralEndpointAmplitude
  rw [cmp89Eq248EntireAliasMomentum_zero]
  ring

/-- Exact factorization of the complete stabilized endpoint numerator into
its common lattice phase and its phase-free central/noncentral amplitude. -/
theorem cmp89Eq251ComplexStabilizedEndpointNumerator_eq_phaseFactor_mul_amplitude
    {L j : ℕ} {mass alpha : ℝ} (z : Fin 4 → ℂ) (mu : Fin 4)
    (holderU endpointU : Fin 4 → ℤ) :
    cmp89Eq251ComplexStabilizedEndpointNumerator 4 L j mass alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq251ComplexEndpointLatticePhaseFactor alpha z holderU endpointU *
        cmp89Eq251ComplexEndpointAmplitude L j mass z mu := by
  rw [cmp89Eq251ComplexStabilizedEndpointNumerator,
    cmp89Eq251ComplexBareEndpoint_zero_eq_phaseFactor_mul_centralAmplitude,
    cmp89Eq251ComplexBareEndpoint_noncentralSum_eq_phaseFactor_mul_sum,
    cmp89Eq251ComplexEndpointAmplitude]
  ring

end

end YangMills.RG
