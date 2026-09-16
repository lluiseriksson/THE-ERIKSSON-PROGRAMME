/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

/-
PRE-VALIDATION IMPORT CONTRACT.

The two imports below name the intended promoted H1 and H2a modules. They do
not exist in the tracked tree yet, so this integration draft is deliberately
not a compilable target until those leaf bricks have been materialized.
-/
import YangMills.RG.BalabanCMP89Eq249PhysicalFineHolderPhaseQuotient
import YangMills.RG.BalabanCMP89Eq249ComplexStripHolderPhaseQuotient

/-!
# PRE-VALIDATION: physical fine-lattice complex Holder phase quotient

This static H2b subbrick has not been compiler-verified and its `.olean` has
not been materialized.

It specializes the global H2a strip estimate to the literal physical
fine-lattice displacement `L^(-j) * u` carried by a unit integer bond. The
local-pair facts are constructed internally:

* the unit bond forces `u != 0`;
* its physical Euclidean length is exactly `L^(-j)`;
* the source scale theorem gives `0 < L^(-j) <= 1`;
* hence the vertical remainder `||L^(-j)u||^(1-alpha)` is at most one.

No arbitrary local-pair hypothesis is accepted. The complete complex alias
momentum remains visible, so this module does not use the unit-lattice alias
phase cancellation refuted by the fine-scale no-go. It also does not
multiply by the endpoint quotient, redistribute radial powers, sum aliases,
construct `B0`, attain window 15, discharge a terminal field or inhabit a
`TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- A unit integer bond cannot be the zero displacement. -/
theorem cmp89Eq251UnitLatticeBondDisplacement_ne_zero_draft
    {d : ℕ} {u : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement u) :
    u ≠ 0 := by
  intro hu
  subst u
  simpa [CMP89Eq251UnitLatticeBondDisplacement,
    cmp89Eq251LatticeL1Length] using hunit

/-- H2a on the physical fine-lattice unit bond. The residual local Holder
power is discharged from the literal scale theorem; it is not a hypothesis
of the endpoint. -/
theorem
    norm_cmp89Eq249PhysicalFine_complexStripPhaseFactor_div_rpow_le_draft
    {L j : ℕ} [NeZero L] {alpha rho : ℝ}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) (hrho : 0 ≤ rho)
    {z : Fin 4 → ℂ} {q : Fin 4 → ℝ}
    (hreal : ∀ mu, (z mu).re = q mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    {u : Fin 4 → ℤ} (hunit : CMP89Eq251UnitLatticeBondDisplacement u) :
    let xi : ℝ := ((L : ℝ) ^ j)⁻¹
    let physicalU := cmp89Eq249PhysicalFineLatticeDisplacement xi u
    ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z physicalU) - 1‖ /
        cmp89Eq251EuclideanNorm physicalU ^ alpha ≤
      2 * Real.exp (2 * rho) *
        (cmp89Eq251EuclideanNorm q ^ alpha + rho) := by
  dsimp only
  obtain ⟨hxi, hxi1⟩ := cmp89Eq245_inverseScale_mem_Ioc L j
  have hu : u ≠ 0 :=
    cmp89Eq251UnitLatticeBondDisplacement_ne_zero_draft hunit
  have hphysical :
      cmp89Eq249PhysicalFineLatticeDisplacement
          (((L : ℝ) ^ j)⁻¹) u ≠ 0 :=
    cmp89Eq249PhysicalFineLatticeDisplacement_ne_zero_draft hxi hu
  have hUeq :
      cmp89Eq251EuclideanNorm
          (cmp89Eq249PhysicalFineLatticeDisplacement
            (((L : ℝ) ^ j)⁻¹) u) =
        ((L : ℝ) ^ j)⁻¹ :=
    cmp89Eq251EuclideanNorm_physicalFineLatticeDisplacement_eq_draft
      hxi.le hunit
  have hpow :
      ((L : ℝ) ^ j)⁻¹ ^ (1 - alpha) ≤ 1 :=
    Real.rpow_le_one hxi.le hxi1 (sub_nonneg.mpr halpha1)
  have hexp :
      Real.exp (2 * rho * ((L : ℝ) ^ j)⁻¹) ≤
        Real.exp (2 * rho) := by
    apply Real.exp_le_exp.mpr
    calc
      2 * rho * ((L : ℝ) ^ j)⁻¹ ≤ 2 * rho * 1 :=
        mul_le_mul_of_nonneg_left hxi1 (mul_nonneg (by norm_num) hrho)
      _ = 2 * rho := mul_one _
  have hinner :
      cmp89Eq251EuclideanNorm q ^ alpha +
          rho * ((L : ℝ) ^ j)⁻¹ ^ (1 - alpha) ≤
        cmp89Eq251EuclideanNorm q ^ alpha + rho := by
    exact add_le_add_left
      (mul_le_mul_of_nonneg_left hpow hrho) _
  have hraw :=
    norm_cmp89Eq251_complexStripPhaseFactor_div_displacement_rpow_le_draft
      halpha0 halpha1 hrho hreal himag hphysical
  calc
    ‖Complex.exp
          (Complex.I * cmp89Eq251EntirePhase z
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (((L : ℝ) ^ j)⁻¹) u)) - 1‖ /
        cmp89Eq251EuclideanNorm
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (((L : ℝ) ^ j)⁻¹) u) ^ alpha ≤
      2 * Real.exp (2 * rho * ((L : ℝ) ^ j)⁻¹) *
        (cmp89Eq251EuclideanNorm q ^ alpha +
          rho * ((L : ℝ) ^ j)⁻¹ ^ (1 - alpha)) := by
      simpa only [hUeq] using hraw
    _ ≤ 2 * Real.exp (2 * rho) *
        (cmp89Eq251EuclideanNorm q ^ alpha +
          rho * ((L : ℝ) ^ j)⁻¹ ^ (1 - alpha)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (by norm_num))
        (add_nonneg
          (Real.rpow_nonneg (cmp89Eq251EuclideanNorm_nonneg q) alpha)
          (mul_nonneg hrho (Real.rpow_nonneg hxi.le (1 - alpha))))
    _ ≤ 2 * Real.exp (2 * rho) *
        (cmp89Eq251EuclideanNorm q ^ alpha + rho) := by
      exact mul_le_mul_of_nonneg_left hinner (by positivity)

end

end YangMills.RG
