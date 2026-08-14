/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatQprimeSignedAliasMomentumDictionary

/-!
# PRE-VALIDATION: centered physical coarse momentum

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been compiler-verified.

The literal Step-7b base momentum uses the nonnegative representative
`ell : Fin N'` and therefore lies in a half-open interval of length `2*pi`,
not in the centered cube consumed by the mass-uniform CMP89 lower bounds.
This module constructs the signed centered representative of `-ell mod N'`,
proves its coordinatewise `pi` bound, and exhibits the exact integer
`2*pi` displacement back to the literal physical momentum.

No denominator is declared periodic here.  In particular, this dictionary
does not identify the central stabilized factor across the displacement.
-/

namespace YangMills.RG

noncomputable section

/-- Coordinatewise centered integer representative of the residue
`-ell mod N'`. -/
def cmp99SourceFlatQprimeCenteredCoarseAlias
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') : Fin d → ℤ :=
  fun mu =>
    (cmp99SourceFlatQprimeSignedCenteredAliasEquiv N' (ell mu)).1

/-- The centered representative belongs to the literal CMP89 half-open
alias interval in every coordinate. -/
theorem cmp99SourceFlatQprimeCenteredCoarseAlias_mem
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') (mu : Fin d) :
    cmp99SourceFlatQprimeCenteredCoarseAlias ell mu ∈
      cmp89Eq245CenteredAliasIntegers N' :=
  (cmp99SourceFlatQprimeSignedCenteredAliasEquiv N' (ell mu)).property

/-- Every integer in the chosen centered half-open interval has doubled
absolute value at most the period count. -/
theorem two_mul_abs_cmp99SourceFlatQprimeCenteredCoarseAlias_le
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') (mu : Fin d) :
    2 * |cmp99SourceFlatQprimeCenteredCoarseAlias ell mu| ≤ (N' : ℤ) := by
  have hm := cmp99SourceFlatQprimeCenteredCoarseAlias_mem ell mu
  rw [cmp89Eq245CenteredAliasIntegers_eq_Ico, Finset.mem_Ico] at hm
  simp only [cmp89Eq245CenteredAliasLower] at hm
  have hhalf : (2 : ℤ) * ((N' / 2 : ℕ) : ℤ) ≤ (N' : ℤ) := by
    omega
  by_cases hnonneg : 0 ≤ cmp99SourceFlatQprimeCenteredCoarseAlias ell mu
  · rw [abs_of_nonneg hnonneg]
    omega
  · rw [abs_of_neg (lt_of_not_ge hnonneg)]
    omega

/-- Real centered base momentum associated with the signed representative. -/
def cmp99SourceFlatQprimeCenteredCoarseBaseMomentum
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') : Fin d → ℝ :=
  fun mu =>
    2 * Real.pi *
      (cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ) / (N' : ℝ)

/-- The centered physical base momentum lies in the exact cube consumed by
the real CMP89 lower bounds. -/
theorem abs_cmp99SourceFlatQprimeCenteredCoarseBaseMomentum_le_pi
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') (mu : Fin d) :
    |cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu| ≤ Real.pi := by
  have hN : 0 < (N' : ℝ) := Nat.cast_pos.mpr (NeZero.pos N')
  have hbound :
      2 * |(cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℝ)| ≤
        (N' : ℝ) := by
    exact_mod_cast
      two_mul_abs_cmp99SourceFlatQprimeCenteredCoarseAlias_le ell mu
  rw [cmp99SourceFlatQprimeCenteredCoarseBaseMomentum, abs_div,
    abs_of_pos hN, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos Real.pi_pos]
  apply (div_le_iff₀ hN).2
  nlinarith [Real.pi_pos]

/-- The literal uncentered physical base momentum differs from the centered
one by a coordinatewise integer multiple of the genuine physical period
`2*pi`. -/
theorem cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum_eq_centered_add_intPeriods
    {d N' : ℕ} [NeZero N'] (ell : FinBox d N') :
    ∃ w : Fin d → ℤ,
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell =
        fun mu =>
          (cmp99SourceFlatQprimeCenteredCoarseBaseMomentum ell mu : ℂ) +
            (w mu : ℂ) * (2 * Real.pi : ℂ) := by
  have hdiv : ∀ mu : Fin d, (N' : ℤ) ∣
      cmp99SourceFlatQprimeCenteredCoarseAlias ell mu + ((ell mu).val : ℤ) := by
    intro mu
    exact cmp99SourceFlatQprimeSignedCenteredAlias_add_quotient_dvd
      N' (ell mu)
  choose c hc using hdiv
  refine ⟨fun mu => -c mu, ?_⟩
  funext mu
  have hN : (N' : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N')
  have hcC := congrArg (fun x : ℤ => (x : ℂ)) (hc mu)
  push_cast at hcC
  have hrep :
      (cmp99SourceFlatQprimeCenteredCoarseAlias ell mu : ℂ) =
        (N' : ℂ) * (c mu : ℂ) - ((ell mu).val : ℂ) := by
    linear_combination hcC
  rw [cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum,
    cmp99SourceFlatQprimeCenteredCoarseBaseMomentum]
  push_cast
  rw [hrep]
  field_simp [hN]
  ring

end

end YangMills.RG
