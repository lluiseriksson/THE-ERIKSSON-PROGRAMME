/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP85SourceAveragingCoefficientFloor
import YangMills.RG.BalabanCMP89Eq249CentralStabilizedAliasDenominator

/-!
# Real lower bound for the stabilized CMP89 (2.49) denominator

Cold compiler evidence: exact source checkpoint
`798e941733bcd934bbab683923452b941f3fb1ea`, GitHub Actions run
`31248239837` (`COLD_MODE=true`, no project-cache restore/save), focal and
audit exit zero, and eight audited declarations with exactly
`[propext, Classical.choice, Quot.sound]`.

The central-pole cancellation exposes a stronger real-slice lower bound than
the earlier multiplied form of (2.50).  The stabilized denominator contains
the term

`a * |u_0(p)|^2`

literally.  Its other two real contributions are nonnegative.  Retaining only
that term therefore gives the scale-uniform floor

`a * ((2 / pi)^d)^2`.

The last theorem replaces the flowing coefficient `a_j` by the positive CMP85
(2.15) floor.  The proof still assumes positive running mass in order to reuse
the existing nonnegativity theorem for every noncentral rational summand; the
lower constant itself is independent of the mass.

No complex strip, complex variation estimate, `B0`, contour displacement, or
regional-Green dictionary is claimed.

Source catalog keys: `cmp89.local-green.fourier.2.34-2.51` and
`cmp85.higgs.averaging-coefficient.2.13-2.15`.
-/

namespace YangMills.RG

noncomputable section

/-- The real noncentral alias sum underlying the stabilized denominator. -/
def cmp89Eq249RealNoncentralAliasSum
    (d L j : ℕ) (mass : ℝ) (p : Fin d → ℝ) : ℝ :=
  ∑ m ∈ (cmp89Eq245CenteredAliasVectors d (L ^ j)).erase
      (cmp89Eq249ZeroAlias d),
    cmp89Eq250AliasDenominatorSummand
      d (((L : ℝ) ^ j)⁻¹) mass p m

/-- The stabilized denominator restricted to real momentum. -/
def cmp89Eq249RealCentralStabilizedAliasDenominator
    (d L j : ℕ) (mass a : ℝ) (p : Fin d → ℝ) : ℝ :=
  cmp89Eq245ScaledLaplacianSymbol
      d (((L : ℝ) ^ j)⁻¹) mass p +
    a * ‖cmp89Eq245ComplexAverageAmplitude
      d (((L : ℝ) ^ j)⁻¹) p‖ ^ 2 +
    a * cmp89Eq245ScaledLaplacianSymbol
      d (((L : ℝ) ^ j)⁻¹) mass p *
      cmp89Eq249RealNoncentralAliasSum d L j mass p

/-- Exact real-slice dictionary for the noncentral rational sum. -/
theorem cmp89Eq249ComplexNoncentralAliasSum_ofReal_eq
    {d L j : ℕ} [NeZero L] {mass : ℝ} {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq249ComplexNoncentralAliasSum d L j mass
        (fun mu => (p mu : ℂ)) =
      (cmp89Eq249RealNoncentralAliasSum d L j mass p : ℂ) := by
  rw [cmp89Eq249ComplexNoncentralAliasSum,
    cmp89Eq249RealNoncentralAliasSum]
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  exact cmp89Eq248ComplexAliasDenominatorSummand_ofReal_eq
    (Finset.mem_of_mem_erase hm) hp

/-- Exact real-slice dictionary for the central averaging pair. -/
theorem cmp89Eq249CentralEntireAveragePair_ofReal_eq
    {d L j : ℕ} [NeZero L] {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq249CentralEntireAveragePair d L j
        (fun mu => (p mu : ℂ)) =
      (‖cmp89Eq245ComplexAverageAmplitude
        d (((L : ℝ) ^ j)⁻¹) p‖ ^ 2 : ℂ) := by
  have hN : 0 < L ^ j :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hzero :
      cmp89Eq249ZeroAlias d ∈ cmp89Eq245CenteredAliasVectors d (L ^ j) :=
    cmp89Eq249ZeroAlias_mem d L j
  have hamp :
      cmp89Eq245EntireAverageAmplitude d (L ^ j)
          (fun mu => (p mu : ℂ)) =
        cmp89Eq245ComplexAverageAmplitude
          d (((L : ℝ) ^ j)⁻¹) p := by
    simpa only [cmp89Eq249ZeroAlias, Pi.zero_apply, Int.cast_zero,
      mul_zero, add_zero, Nat.cast_pow] using
      (cmp89Eq245EntireAverageAmplitude_ofReal_scaled_alias_eq
        (N := L ^ j) hN (m := cmp89Eq249ZeroAlias d) hzero hp)
  rw [cmp89Eq249CentralEntireAveragePair,
    cmp89Eq245EntireAveragePair_ofReal_eq, hamp]

/-- Exact real-slice dictionary for the stabilized denominator. -/
theorem cmp89Eq249CentralStabilizedAliasDenominator_ofReal_eq
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {p : Fin d → ℝ}
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq249CentralStabilizedAliasDenominator d L j mass a
        (fun mu => (p mu : ℂ)) =
      (cmp89Eq249RealCentralStabilizedAliasDenominator
        d L j mass a p : ℂ) := by
  rw [cmp89Eq249CentralStabilizedAliasDenominator,
    cmp89Eq249CentralEntireFineSymbol,
    cmp89Eq245EntireScaledLaplacianSymbol_ofReal_eq,
    cmp89Eq249CentralEntireAveragePair_ofReal_eq hp,
    cmp89Eq249ComplexNoncentralAliasSum_ofReal_eq hp,
    cmp89Eq249RealCentralStabilizedAliasDenominator]
  push_cast
  ring

/-- The noncentral real sum is nonnegative for positive running mass. -/
theorem cmp89Eq249RealNoncentralAliasSum_nonneg
    {d L j : ℕ} {mass : ℝ} {p : Fin d → ℝ}
    (hmass : 0 < mass) :
    0 ≤ cmp89Eq249RealNoncentralAliasSum d L j mass p := by
  rw [cmp89Eq249RealNoncentralAliasSum]
  exact Finset.sum_nonneg fun m _ =>
    cmp89Eq250AliasDenominatorSummand_nonneg m hmass

/-- The explicit central floor of the stabilized denominator. -/
def cmp89Eq249CentralStabilizedLowerConstant (d : ℕ) (a : ℝ) : ℝ :=
  a * ((2 / Real.pi) ^ d) ^ 2

/-- The stabilized real denominator dominates its central averaging term. -/
theorem cmp89Eq249CentralStabilizedLowerConstant_le_real
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {p : Fin d → ℝ}
    (ha : 0 ≤ a) (hmass : 0 < mass)
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
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
    cmp89Eq249RealNoncentralAliasSum_nonneg
      (d := d) (L := L) (j := j) (p := p) hmass
  have htail :
      0 ≤ a * cmp89Eq245ScaledLaplacianSymbol
          d (((L : ℝ) ^ j)⁻¹) mass p *
        cmp89Eq249RealNoncentralAliasSum d L j mass p :=
    mul_nonneg (mul_nonneg ha hcentral) hnoncentral
  rw [cmp89Eq249CentralStabilizedLowerConstant,
    cmp89Eq249RealCentralStabilizedAliasDenominator]
  nlinarith [mul_le_mul_of_nonneg_left hu2 ha]

/-- The stabilized denominator has positive real part on the real cube. -/
theorem cmp89Eq249CentralStabilizedLowerConstant_le_re
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {p : Fin d → ℝ}
    (ha : 0 ≤ a) (hmass : 0 < mass)
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq249CentralStabilizedLowerConstant d a ≤
      (cmp89Eq249CentralStabilizedAliasDenominator d L j mass a
        (fun mu => (p mu : ℂ))).re := by
  rw [cmp89Eq249CentralStabilizedAliasDenominator_ofReal_eq hp]
  exact cmp89Eq249CentralStabilizedLowerConstant_le_real ha hmass hp

/-- Monotonicity of the stabilized lower constant in the source coefficient. -/
theorem cmp89Eq249CentralStabilizedLowerConstant_mono
    {d : ℕ} {a b : ℝ} (hab : a ≤ b) :
    cmp89Eq249CentralStabilizedLowerConstant d a ≤
      cmp89Eq249CentralStabilizedLowerConstant d b := by
  have hfactor : 0 ≤ ((2 / Real.pi) ^ d) ^ 2 := sq_nonneg _
  rw [cmp89Eq249CentralStabilizedLowerConstant,
    cmp89Eq249CentralStabilizedLowerConstant]
  exact mul_le_mul_of_nonneg_right hab hfactor

/-- CMP85 (2.15) supplies a depth-uniform positive floor for the stabilized
CMP89 denominator on the real cube. -/
theorem cmp85Eq215Floor_le_cmp89Eq249CentralStabilizedAliasDenominator_re
    {d L j : ℕ} [NeZero L] {mass a : ℝ}
    (ha : 0 < a) (hL : 1 < L) (hmass : 0 < mass)
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
    (cmp89Eq249CentralStabilizedLowerConstant_le_re
      (cmp99SourceMassParameter_pos ha (lt_trans zero_lt_one hLreal) j).le
      hmass hp)

end

end YangMills.RG
