/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq250CentralAliasLower

/-!
# PRE-VALIDATION: full denominator lower bound in CMP89 (2.50)

The primary source is present, but this module's `.olean` has not yet been
materialized and its declarations have not yet been compiler-verified.

CMP89 (2.45) sums over a centered set of `L^j` reciprocal-lattice aliases in
each coordinate, with shifts `l_mu = 2*pi*m_mu`.  This module constructs that
finite set explicitly, proves that the zero alias belongs to it, defines the
literal denominator in (2.50), and completes its positive lower bound by
retaining only the already sealed central summand.  Every discarded alias is
proved nonnegative; no quantitative noncentral decay is assumed or needed.

The parity split is made on the actual alias count `N = L^j`.  For positive
`j` it agrees with the printed split on the parity of `L`, while it also gives
the coherent singleton set at `j = 0`; no parity dictionary is used below.

This module does not establish the quantitative alias summability (2.51), the
uniform analytic strip, or the Fourier-to-regional-Green dictionary.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Centered integer representatives for a reciprocal-lattice alias set of
cardinality `N`.  The even branch is half-open, exactly as in CMP89 (2.45). -/
def cmp89Eq245CenteredAliasIntegers (N : ℕ) : Finset ℤ :=
  if Even N then
    Finset.Ico (-((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ)
  else
    Finset.Icc (-(((N - 1) / 2 : ℕ) : ℤ)) (((N - 1) / 2 : ℕ) : ℤ)

/-- Every nonempty centered alias interval contains its central integer. -/
theorem zero_mem_cmp89Eq245CenteredAliasIntegers
    {N : ℕ} (hN : 0 < N) :
    (0 : ℤ) ∈ cmp89Eq245CenteredAliasIntegers N := by
  rw [cmp89Eq245CenteredAliasIntegers]
  split_ifs with hEven
  · rcases hEven with ⟨k, hk⟩
    rw [Finset.mem_Ico]
    constructor
    · omega
    · have hhalf : 0 < N / 2 := by omega
      exact_mod_cast hhalf
  · rw [Finset.mem_Icc]
    constructor <;> omega

/-- The `d`-dimensional product of the centered coordinate aliases. -/
def cmp89Eq245CenteredAliasVectors (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => cmp89Eq245CenteredAliasIntegers N)

/-- The all-zero reciprocal-lattice alias belongs to the physical
`L^j`-representative set for every nonzero block size. -/
theorem zero_mem_cmp89Eq245CenteredAliasVectors_pow
    (d L j : ℕ) [NeZero L] :
    (fun _ : Fin d => (0 : ℤ)) ∈ cmp89Eq245CenteredAliasVectors d (L ^ j) := by
  rw [cmp89Eq245CenteredAliasVectors, Fintype.mem_piFinset]
  intro mu
  exact zero_mem_cmp89Eq245CenteredAliasIntegers
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)

/-- The literal reciprocal shift `l'_mu = 2*pi*m'_mu` of CMP89 (2.45). -/
def cmp89Eq245AliasShift {d : ℕ} (m : Fin d → ℤ) : Fin d → ℝ :=
  fun mu => 2 * Real.pi * (m mu : ℝ)

/-- One nonnegative alias summand in the denominator of (2.50). -/
def cmp89Eq250AliasDenominatorSummand
    (d : ℕ) (xi mass : ℝ) (p : Fin d → ℝ) (m : Fin d → ℤ) : ℝ :=
  ‖cmp89Eq245ComplexAverageAmplitude d xi
      (fun mu => p mu + cmp89Eq245AliasShift m mu)‖ ^ 2 /
    cmp89Eq245ScaledLaplacianSymbol d xi mass
      (fun mu => p mu + cmp89Eq245AliasShift m mu)

/-- Positive mass makes every alias summand nonnegative. -/
theorem cmp89Eq250AliasDenominatorSummand_nonneg
    {d : ℕ} {xi mass : ℝ} {p : Fin d → ℝ} (m : Fin d → ℤ)
    (hmass : 0 < mass) :
    0 ≤ cmp89Eq250AliasDenominatorSummand d xi mass p m := by
  have hden :
      0 < cmp89Eq245ScaledLaplacianSymbol d xi mass
        (fun mu => p mu + cmp89Eq245AliasShift m mu) := by
    rw [cmp89Eq245ScaledLaplacianSymbol]
    exact add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (pow_pos hmass 2)
  exact div_nonneg (sq_nonneg _) hden.le

/-- The complete denominator appearing in CMP89 (2.49)--(2.50), after the
printed multiplication by `Delta^1(p)`. -/
def cmp89Eq250FullAliasDenominator
    (d L j : ℕ) (mass a : ℝ) (p : Fin d → ℝ) : ℝ :=
  a * (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
      cmp89Eq250AliasDenominatorSummand
        d (((L : ℝ) ^ j)⁻¹) mass p m) *
      cmp89Eq249UnitLaplacianSymbol d mass p +
    cmp89Eq249UnitLaplacianSymbol d mass p

/-- The zero alias summand is definitionally the central source term. -/
theorem cmp89Eq250AliasDenominatorSummand_zero
    (d : ℕ) (xi mass : ℝ) (p : Fin d → ℝ) :
    cmp89Eq250AliasDenominatorSummand d xi mass p (fun _ => 0) =
      ‖cmp89Eq245ComplexAverageAmplitude d xi p‖ ^ 2 /
        cmp89Eq245ScaledLaplacianSymbol d xi mass p := by
  simp [cmp89Eq250AliasDenominatorSummand, cmp89Eq245AliasShift]

/-- The complete denominator dominates the literal central alias retained in
the first inequality of CMP89 (2.50). -/
theorem cmp89Eq250LiteralCentralAliasContribution_le_full_denominator
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {p : Fin d → ℝ}
    (ha : 0 ≤ a) (hmass : 0 < mass) :
    cmp89Eq250LiteralCentralAliasContribution
        d (((L : ℝ) ^ j)⁻¹) mass a p ≤
      cmp89Eq250FullAliasDenominator d L j mass a p := by
  let zeroAlias : Fin d → ℤ := fun _ => 0
  have hzero :
      zeroAlias ∈ cmp89Eq245CenteredAliasVectors d (L ^ j) :=
    zero_mem_cmp89Eq245CenteredAliasVectors_pow d L j
  have hsum :
      cmp89Eq250AliasDenominatorSummand
          d (((L : ℝ) ^ j)⁻¹) mass p zeroAlias ≤
        ∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
          cmp89Eq250AliasDenominatorSummand
            d (((L : ℝ) ^ j)⁻¹) mass p m := by
    exact Finset.single_le_sum
      (fun m _ => cmp89Eq250AliasDenominatorSummand_nonneg m hmass) hzero
  have hunit : 0 ≤ cmp89Eq249UnitLaplacianSymbol d mass p := by
    rw [cmp89Eq249UnitLaplacianSymbol]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hsum ha
  have hweighted := mul_le_mul_of_nonneg_right hscaled hunit
  rw [cmp89Eq250FullAliasDenominator]
  calc
    cmp89Eq250LiteralCentralAliasContribution
        d (((L : ℝ) ^ j)⁻¹) mass a p =
        a * cmp89Eq250AliasDenominatorSummand
          d (((L : ℝ) ^ j)⁻¹) mass p zeroAlias *
          cmp89Eq249UnitLaplacianSymbol d mass p := by
      rw [cmp89Eq250LiteralCentralAliasContribution]
      simp only [zeroAlias, cmp89Eq250AliasDenominatorSummand_zero]
      ring
    _ ≤ a * (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
          cmp89Eq250AliasDenominatorSummand
            d (((L : ℝ) ^ j)⁻¹) mass p m) *
        cmp89Eq249UnitLaplacianSymbol d mass p := hweighted
    _ ≤ a * (∑ m ∈ cmp89Eq245CenteredAliasVectors d (L ^ j),
          cmp89Eq250AliasDenominatorSummand
            d (((L : ℝ) ^ j)⁻¹) mass p m) *
          cmp89Eq249UnitLaplacianSymbol d mass p +
        cmp89Eq249UnitLaplacianSymbol d mass p :=
      le_add_of_nonneg_right hunit

/-- Full source denominator form of the positive lower bound (2.50). -/
theorem cmp89Eq250CentralAliasLowerConstant_le_full_denominator
    {d L j : ℕ} [NeZero L] {mass a : ℝ} {p : Fin d → ℝ}
    (ha : 0 ≤ a) (hmass : 0 < mass)
    (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq250CentralAliasLowerConstant d a ≤
      cmp89Eq250FullAliasDenominator d L j mass a p :=
  (cmp89Eq250CentralAliasLowerConstant_le_literal_inverseScale ha hmass hp).trans
    (cmp89Eq250LiteralCentralAliasContribution_le_full_denominator ha hmass)

end

end YangMills.RG
