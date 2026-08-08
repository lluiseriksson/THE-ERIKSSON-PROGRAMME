/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251AliasAmplitudeUpper

/-!
# PRE-VALIDATION: noncentral Laplacian ratio in CMP89 (2.51)

The source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

CMP89 printed p. 585 compares the two massive symbols by

`O(1) * (|p|^2 + m_j^2) / (|p+l|^2 + m_j^2)`.

This module proves that literal comparison for the repository symbols, using
the expanded-zone difference bound already sealed for every printed alias.
It then names the extra uniform mass window `mass^2 <= 1` and derives the
inverse-square noncentral estimate needed in (2.51).  The mass window is an
explicit hypothesis: the dictionary showing that the source family `m_j`
lies in it remains open and is not hidden in an `O(1)` constant.

No Holder factor, complete integrand estimate, complex strip, or transport to
the regional Green is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Euclidean momentum square used literally in the comparison below (2.49). -/
def cmp89Eq251MomentumSquare {d : ℕ} (p : Fin d → ℝ) : ℝ :=
  ∑ mu, (p mu) ^ 2

theorem cmp89Eq251MomentumSquare_nonneg
    {d : ℕ} (p : Fin d → ℝ) :
    0 ≤ cmp89Eq251MomentumSquare p := by
  rw [cmp89Eq251MomentumSquare]
  exact Finset.sum_nonneg fun mu _ => sq_nonneg (p mu)

/-- The unit-lattice difference is bounded above by continuum momentum. -/
theorem cmp89Eq249UnitDifferenceNorm_le_abs (p : ℝ) :
    cmp89Eq249UnitDifferenceNorm p ≤ |p| := by
  simpa [cmp89Eq245ScaledDifferenceNorm,
    cmp89Eq249UnitDifferenceNorm] using
      (cmp89Eq245ScaledDifferenceNorm_le_abs (xi := (1 : ℝ))
        (p := p) (by norm_num))

/-- The unit massive symbol is at most the continuum momentum square plus
the same mass square. -/
theorem cmp89Eq249UnitLaplacianSymbol_le_momentumSquare
    {d : ℕ} (mass : ℝ) (p : Fin d → ℝ) :
    cmp89Eq249UnitLaplacianSymbol d mass p ≤
      cmp89Eq251MomentumSquare p + mass ^ 2 := by
  rw [cmp89Eq249UnitLaplacianSymbol, cmp89Eq251MomentumSquare]
  gcongr with mu
  exact (sq_le_sq₀ (norm_nonneg _ ) (abs_nonneg _)).2
    (cmp89Eq249UnitDifferenceNorm_le_abs (p mu))

/-- On the expanded alias zone, the scaled massive symbol is bounded below
by the explicit continuum symbol with coefficient `(1/(3*pi))^2`. -/
theorem one_div_three_pi_sq_mul_momentumSquare_le_scaledLaplacian
    {d : ℕ} {xi mass : ℝ} {q : Fin d → ℝ}
    (hxi : 0 < xi)
    (hq : ∀ mu, |xi * q mu| ≤ 3 * Real.pi / 2) :
    (1 / (3 * Real.pi)) ^ 2 *
        (cmp89Eq251MomentumSquare q + mass ^ 2) ≤
      cmp89Eq245ScaledLaplacianSymbol d xi mass q := by
  have hcNonneg : 0 ≤ 1 / (3 * Real.pi) := by positivity
  have hcOne : (1 / (3 * Real.pi)) ^ 2 ≤ 1 := by
    have hden : 1 ≤ 3 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hfrac : 1 / (3 * Real.pi) ≤ 1 :=
      (div_le_one (by positivity : 0 < 3 * Real.pi)).2 hden
    nlinarith
  rw [cmp89Eq251MomentumSquare,
    cmp89Eq245ScaledLaplacianSymbol, mul_add, Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro mu _
    have hcoord :=
      one_div_three_pi_mul_abs_le_cmp89Eq245ScaledDifferenceNorm
        hxi (hq mu)
    have hsquare := (sq_le_sq₀
      (mul_nonneg hcNonneg (abs_nonneg (q mu))) (norm_nonneg _)).2 hcoord
    simpa [sq_abs, mul_pow] using hsquare
  · exact mul_le_of_le_one_left (sq_nonneg mass)
      hcOne

/-- Literal two-symbol comparison printed immediately before (2.51).  No
upper mass restriction is used here. -/
theorem cmp89Eq249_unit_div_scaled_le_momentum_ratio
    {d : ℕ} {xi mass : ℝ} {p q : Fin d → ℝ}
    (hxi : 0 < xi)
    (hqZone : ∀ mu, |xi * q mu| ≤ 3 * Real.pi / 2)
    (hden : 0 < cmp89Eq251MomentumSquare q + mass ^ 2) :
    cmp89Eq249UnitLaplacianSymbol d mass p /
        cmp89Eq245ScaledLaplacianSymbol d xi mass q ≤
      (3 * Real.pi) ^ 2 *
        (cmp89Eq251MomentumSquare p + mass ^ 2) /
          (cmp89Eq251MomentumSquare q + mass ^ 2) := by
  have hunit := cmp89Eq249UnitLaplacianSymbol_le_momentumSquare mass p
  have hscaled :=
    one_div_three_pi_sq_mul_momentumSquare_le_scaledLaplacian
      hxi hqZone
  have hcPos : 0 < (1 / (3 * Real.pi)) ^ 2 := by positivity
  have hscaledPos :
      0 < cmp89Eq245ScaledLaplacianSymbol d xi mass q :=
    (mul_pos hcPos hden).trans_le hscaled
  apply (div_le_iff₀ hscaledPos).2
  apply hunit.trans
  have hcoefNonneg :
      0 ≤ (3 * Real.pi) ^ 2 *
        (cmp89Eq251MomentumSquare p + mass ^ 2) /
          (cmp89Eq251MomentumSquare q + mass ^ 2) := by positivity
  calc
    cmp89Eq251MomentumSquare p + mass ^ 2 =
        ((3 * Real.pi) ^ 2 *
          (cmp89Eq251MomentumSquare p + mass ^ 2) /
            (cmp89Eq251MomentumSquare q + mass ^ 2)) *
          ((1 / (3 * Real.pi)) ^ 2 *
            (cmp89Eq251MomentumSquare q + mass ^ 2)) := by
      field_simp [ne_of_gt hden, Real.pi_ne_zero]
      ring
    _ ≤ ((3 * Real.pi) ^ 2 *
          (cmp89Eq251MomentumSquare p + mass ^ 2) /
            (cmp89Eq251MomentumSquare q + mass ^ 2)) *
          cmp89Eq245ScaledLaplacianSymbol d xi mass q :=
      mul_le_mul_of_nonneg_left hscaled hcoefNonneg

/-- The explicit uniform small-mass window needed to turn the literal source
ratio into scale-independent noncentral inverse-square decay. -/
def CMP89Eq251UniformMassWindow (mass : ℝ) : Prop :=
  mass ^ 2 ≤ 1

/-- Every nonzero printed alias has strictly positive continuum momentum
square, even when the mass vanishes. -/
theorem cmp89Eq251MomentumSquare_shift_pos
    {d : ℕ} {m : Fin d → ℤ} (hm0 : m ≠ 0) {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    0 < cmp89Eq251MomentumSquare
      (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) := by
  have hex : ∃ mu, m mu ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (funext h)
  obtain ⟨mu, hmu⟩ := hex
  have hqLower := pi_mul_abs_cast_le_abs_add_alias (hp mu) hmu
  have hmuReal : (m mu : ℝ) ≠ 0 := by exact_mod_cast hmu
  have hqPos :
      0 < |p mu + 2 * Real.pi * (m mu : ℝ)| :=
    (mul_pos Real.pi_pos (abs_pos.mpr hmuReal)).trans_le hqLower
  rw [cmp89Eq251MomentumSquare]
  apply Finset.sum_pos'
  · intro nu _
    exact sq_nonneg _
  · exact ⟨mu, Finset.mem_univ mu,
      sq_pos_of_ne_zero (abs_pos.mp hqPos)⟩

/-- Source-specialized noncentral inverse-square bound.  The dimension and
the unit mass window remain visible in the constant. -/
theorem cmp89Eq249_unit_div_scaled_noncentral_alias_le
    {d N : ℕ} (hN : 0 < N) {mass : ℝ}
    (hmass : CMP89Eq251UniformMassWindow mass)
    {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    (hm0 : m ≠ 0) {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq249UnitLaplacianSymbol d mass p /
        cmp89Eq245ScaledLaplacianSymbol d (N : ℝ)⁻¹ mass
          (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) ≤
      ((3 * Real.pi) ^ 2 * ((d : ℝ) * Real.pi ^ 2 + 1)) /
        cmp89Eq251MomentumSquare
          (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) := by
  change mass ^ 2 ≤ 1 at hmass
  let q : Fin d → ℝ := fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  have hNReal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hqPos : 0 < cmp89Eq251MomentumSquare q :=
    cmp89Eq251MomentumSquare_shift_pos hm0 hp
  have hden : 0 < cmp89Eq251MomentumSquare q + mass ^ 2 :=
    add_pos_of_pos_of_nonneg hqPos (sq_nonneg mass)
  have hratio := cmp89Eq249_unit_div_scaled_le_momentum_ratio
    (xi := (N : ℝ)⁻¹) (mass := mass) (p := p) (q := q)
    (inv_pos.mpr hNReal)
    (fun mu =>
      abs_inverse_count_mul_add_cmp89Eq245AliasShift_le_three_pi_div_two
        hN (by
          rw [cmp89Eq245CenteredAliasVectors,
            Fintype.mem_piFinset] at hm
          exact hm mu) (hp mu)) hden
  have hpSquare :
      cmp89Eq251MomentumSquare p ≤ (d : ℝ) * Real.pi ^ 2 := by
    rw [cmp89Eq251MomentumSquare]
    calc
      (∑ mu, p mu ^ 2) ≤ ∑ _mu : Fin d, Real.pi ^ 2 := by
        apply Finset.sum_le_sum
        intro mu _
        exact (sq_le_sq₀ (abs_nonneg _) Real.pi_pos.le).2 (hp mu)
      _ = (d : ℝ) * Real.pi ^ 2 := by
        rw [Fin.sum_const, nsmul_eq_mul]
  have hnum :
      cmp89Eq251MomentumSquare p + mass ^ 2 ≤
        (d : ℝ) * Real.pi ^ 2 + 1 := add_le_add hpSquare hmass
  apply hratio.trans
  have hcNonneg : 0 ≤ (3 * Real.pi) ^ 2 := sq_nonneg _
  calc
    (3 * Real.pi) ^ 2 *
          (cmp89Eq251MomentumSquare p + mass ^ 2) /
            (cmp89Eq251MomentumSquare q + mass ^ 2) ≤
        (3 * Real.pi) ^ 2 *
          ((d : ℝ) * Real.pi ^ 2 + 1) /
            (cmp89Eq251MomentumSquare q + mass ^ 2) := by
      gcongr
    _ ≤ ((3 * Real.pi) ^ 2 * ((d : ℝ) * Real.pi ^ 2 + 1)) /
          cmp89Eq251MomentumSquare q := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hqPos
      · exact le_add_of_nonneg_right (sq_nonneg mass)

end

end YangMills.RG
