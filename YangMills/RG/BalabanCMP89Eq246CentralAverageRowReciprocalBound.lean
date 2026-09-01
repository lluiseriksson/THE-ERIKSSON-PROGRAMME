/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246FinePointSourceMomentBound

/-!
# PRE-VALIDATION: scale-uniform reciprocal bound for the central Eq. (2.46) row

The central branch of the full fine-point-source solution divides by the
central opposite-momentum averaging row. Nonvanishing alone is not enough for
the subsequent quantitative solution bound. This module derives the literal
reciprocal estimate from the already named lower floor of the central
averaging pair and the strip upper bound for its column factor.

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

This is a quantitative leaf below the full-solution bound. It makes no claim
about CMP89 (2.42), uniform physical `B0`/`delta0`, window 15, terminal rows,
`20/41`, or `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit reciprocal budget for the central opposite-momentum row. -/
def cmp89Eq246CentralAverageRowReciprocalBound (rho : ℝ) : ℝ :=
  Real.exp rho ^ 4 /
    (cmp89Eq249CentralAveragePairLowerConstant -
      cmp89Eq249CentralAveragePairVerticalBound rho)

/-- The central-pair strip window quantitatively controls the reciprocal of
the row factor used by the central branch of the full Eq. (2.46) solution. -/
theorem norm_inv_cmp89Eq246CentralAverageRow_le
    {L j : ℕ} [NeZero L] {rho : ℝ} (hrho : 0 ≤ rho)
    (hwindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    {z : Fin 4 → ℂ}
    (hreal : ∀ mu, (z mu).re = p mu)
    (himag : ∀ mu, |(z mu).im| ≤ rho) :
    ‖(cmp89Eq246EntireAliasAverageRow 4 L j z
        (cmp89Eq249CentralAliasIndex 4 L j))⁻¹‖ ≤
      cmp89Eq246CentralAverageRowReciprocalBound rho := by
  let central := cmp89Eq249CentralAliasIndex 4 L j
  let column := cmp89Eq246EntireAliasAverageColumn 4 L j z central
  let row := cmp89Eq246EntireAliasAverageRow 4 L j z central
  let gap := cmp89Eq249CentralAveragePairLowerConstant -
    cmp89Eq249CentralAveragePairVerticalBound rho
  have hgap : 0 < gap := by
    simpa [gap, CMP89Eq249CentralAveragePairComplexWindow] using hwindow
  have hpairLower : gap ≤
      ‖cmp89Eq249CentralEntireAveragePair 4 L j z‖ := by
    simpa [gap] using
      sub_variation_le_norm_cmp89Eq249CentralEntireAveragePair
        (L := L) (j := j) hrho hp hreal himag
  have hzeroMomentum :
      cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias 4) = z := by
    funext mu
    simp [cmp89Eq248EntireAliasMomentum, cmp89Eq249ZeroAlias,
      cmp89Eq245AliasShift]
  have hpair : column * row =
      cmp89Eq249CentralEntireAveragePair 4 L j z := by
    change cmp89Eq245EntireAverageAmplitude 4 (L ^ j)
          (cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias 4)) *
        cmp89Eq245EntireAverageAmplitude 4 (L ^ j)
          (-cmp89Eq248EntireAliasMomentum z (cmp89Eq249ZeroAlias 4)) =
      cmp89Eq245EntireAverageAmplitude 4 (L ^ j) z *
        cmp89Eq245EntireAverageAmplitude 4 (L ^ j) (-z)
    rw [hzeroMomentum]
  have hcolumn : ‖column‖ ≤ Real.exp rho ^ 4 := by
    simpa [column, central, cmp89Eq246EntireAliasAverageColumn,
      cmp89Eq248EntireAliasMomentum_zero] using
      (norm_cmp89Eq245EntireAverageAmplitude_le_exp_pow
        (d := 4) (N := L ^ j)
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
        hrho (fun mu => by simpa using himag mu))
  have hgapRow : gap ≤ Real.exp rho ^ 4 * ‖row‖ := by
    calc
      gap ≤ ‖cmp89Eq249CentralEntireAveragePair 4 L j z‖ := hpairLower
      _ = ‖column‖ * ‖row‖ := by rw [← hpair, norm_mul]
      _ ≤ Real.exp rho ^ 4 * ‖row‖ := by
        exact mul_le_mul_of_nonneg_right hcolumn (norm_nonneg row)
  have hpairNe : cmp89Eq249CentralEntireAveragePair 4 L j z ≠ 0 :=
    cmp89Eq249CentralEntireAveragePair_ne_zero
      (L := L) (j := j) hrho hwindow hp hreal himag
  have hrowNe : row ≠ 0 := by
    simpa [row, central] using
      cmp89Eq246CentralAverageRow_ne_zero_of_pair_ne_zero 4 L j z hpairNe
  have hrowPos : 0 < ‖row‖ := norm_pos_iff.mpr hrowNe
  rw [norm_inv, inv_eq_one_div,
    cmp89Eq246CentralAverageRowReciprocalBound]
  change 1 / ‖row‖ ≤ Real.exp rho ^ 4 / gap
  exact (div_le_div_iff₀ hrowPos hgap).2 (by simpa using hgapRow)

end

end YangMills.RG
