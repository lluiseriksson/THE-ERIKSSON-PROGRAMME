/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249CentralStabilizedRealLower
import YangMills.RG.BalabanCMP89Eq251NoncentralRealIntegrandBound

/-!
# Mass-uniform real gap for noncentral CMP89 aliases

Cold compiler evidence: exact source checkpoint
`5ad7d83a3398438d1ec992167127843b439c587a`, GitHub Actions run
`31249442951` (`COLD_MODE=true`, no project-cache restore/save), focal and
audit exit zero, and seven audited declarations with exactly
`[propext, Classical.choice, Quot.sound]`.

For a nonzero printed reciprocal alias, the shifted real momentum has
Euclidean norm at least `pi`.  Combining that fact with the expanded-zone
difference estimate gives the literal mass-independent lower bound

`1 / 9 <= Delta_l`.

Consequently every noncentral rational summand is nonnegative even at zero
mass.  This removes the temporary `mass > 0` premise from the real lower bound
for the central-stabilized denominator and from its CMP85-uniform
specialization.

No complex neighborhood, variation estimate, strip radius, `B0`, contour
shift, or regional-Green dictionary is claimed.

Source catalog keys: `cmp89.local-green.fourier.2.34-2.51` and
`cmp85.higgs.averaging-coefficient.2.13-2.15`.
-/

namespace YangMills.RG

noncomputable section

/-- Every nonzero printed alias has a scale- and mass-independent real gap
in its fine-lattice symbol. -/
theorem one_div_nine_le_cmp89Eq245ScaledLaplacianSymbol_noncentral_alias
    {d N : ℕ} (hN : 0 < N) {mass : ℝ}
    {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    (hm0 : m ≠ 0) {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    (1 : ℝ) / 9 ≤
      cmp89Eq245ScaledLaplacianSymbol d (N : ℝ)⁻¹ mass
        (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) := by
  let q : Fin d → ℝ := fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnorm : Real.pi ≤ cmp89Eq251EuclideanNorm q :=
    pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp
  have hnormNonneg : 0 ≤ cmp89Eq251EuclideanNorm q :=
    cmp89Eq251EuclideanNorm_nonneg q
  have hmomentum : Real.pi ^ 2 ≤ cmp89Eq251MomentumSquare q := by
    rw [← sq_cmp89Eq251EuclideanNorm q]
    exact (sq_le_sq₀ Real.pi_pos.le hnormNonneg).2 hnorm
  have hzone : ∀ mu, |(N : ℝ)⁻¹ * q mu| ≤ 3 * Real.pi / 2 := by
    intro mu
    exact abs_inverse_count_mul_add_cmp89Eq245AliasShift_le_three_pi_div_two
      hN (by
        rw [cmp89Eq245CenteredAliasVectors, Fintype.mem_piFinset] at hm
        exact hm mu) (hp mu)
  have hscaled :=
    one_div_three_pi_sq_mul_momentumSquare_le_scaledLaplacian
      (d := d) (xi := (N : ℝ)⁻¹) (mass := mass) (q := q)
      (inv_pos.mpr hNreal) hzone
  calc
    (1 : ℝ) / 9 =
        (1 / (3 * Real.pi)) ^ 2 * Real.pi ^ 2 := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ (1 / (3 * Real.pi)) ^ 2 * cmp89Eq251MomentumSquare q := by
      exact mul_le_mul_of_nonneg_left hmomentum (sq_nonneg _)
    _ ≤ (1 / (3 * Real.pi)) ^ 2 *
          (cmp89Eq251MomentumSquare q + mass ^ 2) := by
      gcongr
      exact le_add_of_nonneg_right (sq_nonneg mass)
    _ ≤ cmp89Eq245ScaledLaplacianSymbol d (N : ℝ)⁻¹ mass q := hscaled

/-- The noncentral fine-lattice denominator is strictly positive without a
positive-mass assumption. -/
theorem cmp89Eq245ScaledLaplacianSymbol_noncentral_alias_pos
    {d N : ℕ} (hN : 0 < N) {mass : ℝ}
    {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    (hm0 : m ≠ 0) {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    0 < cmp89Eq245ScaledLaplacianSymbol d (N : ℝ)⁻¹ mass
      (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) :=
  (by norm_num : (0 : ℝ) < 1 / 9).trans_le
    (one_div_nine_le_cmp89Eq245ScaledLaplacianSymbol_noncentral_alias
      hN hm hm0 hp)

/-- Every noncentral alias summand is nonnegative, uniformly down to zero
running mass. -/
theorem cmp89Eq250AliasDenominatorSummand_noncentral_nonneg
    {d N : ℕ} (hN : 0 < N) {mass : ℝ}
    {m : Fin d → ℤ}
    (hm : m ∈ cmp89Eq245CenteredAliasVectors d N)
    (hm0 : m ≠ 0) {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    0 ≤ cmp89Eq250AliasDenominatorSummand
      d (N : ℝ)⁻¹ mass p m := by
  rw [cmp89Eq250AliasDenominatorSummand]
  exact div_nonneg (sq_nonneg _)
    (cmp89Eq245ScaledLaplacianSymbol_noncentral_alias_pos
      hN hm hm0 hp).le

/-- The complete noncentral real alias sum is nonnegative without any mass
lower bound. -/
theorem cmp89Eq249RealNoncentralAliasSum_nonneg_massUniform
    {d L j : ℕ} [NeZero L] {mass : ℝ} {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    0 ≤ cmp89Eq249RealNoncentralAliasSum d L j mass p := by
  let aliases : Finset (Fin d → ℤ) :=
    cmp89Eq245CenteredAliasVectors d (L ^ j)
  let zeroAlias : Fin d → ℤ := cmp89Eq249ZeroAlias d
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  rw [cmp89Eq249RealNoncentralAliasSum]
  change 0 ≤ ∑ m ∈ aliases.erase zeroAlias,
    cmp89Eq250AliasDenominatorSummand
      d (((L : ℝ) ^ j)⁻¹) mass p m
  apply Finset.sum_nonneg
  intro m hm
  have hmParts := Finset.mem_erase.mp hm
  have hmMem : m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j) := by
    simpa only [aliases] using hmParts.2
  have hm0 : m ≠ 0 := by
    simpa only [zeroAlias, cmp89Eq249ZeroAlias] using hmParts.1
  simpa only [Nat.cast_pow] using
    (cmp89Eq250AliasDenominatorSummand_noncentral_nonneg
      (d := d) (N := L ^ j) (mass := mass) (m := m) (p := p)
      hN hmMem hm0 hp)

/-- The stabilized real lower bound is independent of the running mass. -/
theorem cmp89Eq249CentralStabilizedLowerConstant_le_real_massUniform
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {p : Fin d → ℝ}
    (ha : 0 ≤ a) (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq249CentralStabilizedLowerConstant d a ≤
      cmp89Eq249RealCentralStabilizedAliasDenominator
        d L j mass a p := by
  have hu :=
    pow_two_div_pi_le_norm_cmp89Eq245ComplexAverageAmplitude_inverseScale
      (d := d) (L := L) (j := j) hp
  have hu0 : 0 ≤ (2 / Real.pi) ^ d :=
    pow_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) d
  have hu2 :
      ((2 / Real.pi) ^ d) ^ 2 ≤
        ‖cmp89Eq245ComplexAverageAmplitude
          d (((L : ℝ) ^ j)⁻¹) p‖ ^ 2 :=
    (sq_le_sq₀ hu0 (norm_nonneg _)).2 hu
  have hcentral :
      0 ≤ cmp89Eq245ScaledLaplacianSymbol
        d (((L : ℝ) ^ j)⁻¹) mass p := by
    rw [cmp89Eq245ScaledLaplacianSymbol]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hnoncentral :=
    cmp89Eq249RealNoncentralAliasSum_nonneg_massUniform
      (d := d) (L := L) (j := j) (mass := mass) hp
  have htail :
      0 ≤ a * cmp89Eq245ScaledLaplacianSymbol
          d (((L : ℝ) ^ j)⁻¹) mass p *
        cmp89Eq249RealNoncentralAliasSum d L j mass p :=
    mul_nonneg (mul_nonneg ha hcentral) hnoncentral
  rw [cmp89Eq249CentralStabilizedLowerConstant,
    cmp89Eq249RealCentralStabilizedAliasDenominator]
  nlinarith [mul_le_mul_of_nonneg_left hu2 ha]

/-- Mass-uniform positive-real-part form of the stabilized lower bound. -/
theorem cmp89Eq249CentralStabilizedLowerConstant_le_re_massUniform
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {p : Fin d → ℝ}
    (ha : 0 ≤ a) (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq249CentralStabilizedLowerConstant d a ≤
      (cmp89Eq249CentralStabilizedAliasDenominator d L j mass a
        (fun mu => (p mu : ℂ))).re := by
  rw [cmp89Eq249CentralStabilizedAliasDenominator_ofReal_eq hp]
  exact cmp89Eq249CentralStabilizedLowerConstant_le_real_massUniform ha hp

/-- CMP85 (2.15) supplies a depth- and mass-uniform positive floor for the
stabilized CMP89 denominator on the real cube. -/
theorem cmp85Eq215Floor_le_cmp89Eq249CentralStabilizedAliasDenominator_re_massUniform
    {d L j : ℕ} [NeZero L] {mass a : ℝ}
    (ha : 0 < a) (hL : 1 < L)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq249CentralStabilizedLowerConstant d
        (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) ≤
      (cmp89Eq249CentralStabilizedAliasDenominator d L j mass
        (cmp99SourceMassParameter a (L : ℝ) j)
        (fun mu => (p mu : ℂ))).re := by
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hfloor :=
    cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter ha hLreal j
  exact (cmp89Eq249CentralStabilizedLowerConstant_mono hfloor).trans
    (cmp89Eq249CentralStabilizedLowerConstant_le_re_massUniform
      (cmp99SourceMassParameter_pos ha (lt_trans zero_lt_one hLreal) j).le hp)

end

end YangMills.RG
