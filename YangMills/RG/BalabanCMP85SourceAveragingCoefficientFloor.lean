/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceMassWeights
import YangMills.RG.BalabanCMP89Eq250FullDenominatorLower

/-!
# The uniform CMP85 averaging-coefficient floor

Compiler-verified at exact source checkpoint
`e0aaffdc9afc669bcef22aa040768beaf1b88df8` by cold GitHub Actions run
`31245326067`. Restoration and saving of `.lake/build` were skipped; the
focal and five-declaration audit exited zero.

CMP85 (2.13), printed p. 609, gives the recursion

`a_{k+1} = a * a_k / (a * L^(-2) + a_k)`, with `a_1 = a`,

and (2.15) identifies its decreasing positive limit as
`a * (1 - L^(-2))`.  The existing CMP99 source dictionary already uses the
same recursion, with Lean index `j = k - 1`.  This module proves directly from
that recursive object that the printed limit is a uniform lower floor, then
feeds it into the cold-sealed real denominator bound of CMP89 (2.50).

This is a real-slice gap only.  It does not construct a complex strip, a
uniform complex bound `B0(delta0)`, the regional Green dictionary, or attain
window 15.

Source catalog key: `cmp85.higgs.averaging-coefficient.2.13-2.15`.
-/

namespace YangMills.RG

noncomputable section

/-- The positive limiting coefficient printed in CMP85 (2.15). -/
def cmp85Eq215SourceAveragingCoefficientFloor (a L : ℝ) : ℝ :=
  a * (1 - (L ^ 2)⁻¹)

/-- The printed limiting coefficient is positive in the physical regime. -/
theorem cmp85Eq215SourceAveragingCoefficientFloor_pos
    {a L : ℝ} (ha : 0 < a) (hL : 1 < L) :
    0 < cmp85Eq215SourceAveragingCoefficientFloor a L := by
  have hLplus : 0 < L + 1 := by linarith
  have hLsq : 1 < L ^ 2 := by
    have hprod : 0 < (L - 1) * (L + 1) :=
      mul_pos (sub_pos.mpr hL) hLplus
    nlinarith
  rw [cmp85Eq215SourceAveragingCoefficientFloor]
  exact mul_pos ha (sub_pos.mpr (inv_lt_one_of_one_lt₀ hLsq))

/-- CMP85 (2.15), in the direction needed downstream: every coefficient of
the recursively generated source flow stays above its positive limiting
value. -/
theorem cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter
    {a L : ℝ} (ha : 0 < a) (hL : 1 < L) :
    ∀ j, cmp85Eq215SourceAveragingCoefficientFloor a L ≤
      cmp99SourceMassParameter a L j := by
  intro j
  induction j with
  | zero =>
      rw [cmp99SourceMassParameter_zero,
        cmp85Eq215SourceAveragingCoefficientFloor]
      have hLpos : 0 < L := lt_trans zero_lt_one hL
      have hinv : 0 ≤ (L ^ 2)⁻¹ :=
        (inv_nonneg.mpr (sq_nonneg L))
      nlinarith [mul_nonneg ha.le hinv]
  | succ j ih =>
      rw [cmp99SourceMassParameter_succ]
      have hLpos : 0 < L := lt_trans zero_lt_one hL
      have hinv : 0 < (L ^ 2)⁻¹ :=
        inv_pos.mpr (sq_pos_of_pos hLpos)
      have hmass : 0 < cmp99SourceMassParameter a L j :=
        cmp99SourceMassParameter_pos ha hLpos j
      have hden :
          0 < a * (L ^ 2)⁻¹ + cmp99SourceMassParameter a L j :=
        add_pos (mul_pos ha hinv) hmass
      apply (le_div_iff₀ hden).2
      have hdiff :
          0 ≤ cmp99SourceMassParameter a L j -
            cmp85Eq215SourceAveragingCoefficientFloor a L :=
        sub_nonneg.mpr ih
      have hprod :
          0 ≤ a * (L ^ 2)⁻¹ *
            (cmp99SourceMassParameter a L j -
              cmp85Eq215SourceAveragingCoefficientFloor a L) :=
        mul_nonneg (mul_nonneg ha.le hinv.le) hdiff
      rw [cmp85Eq215SourceAveragingCoefficientFloor] at hprod ⊢
      nlinarith

/-- Monotonicity of the explicit CMP89 central lower constant in its source
coefficient. -/
theorem cmp89Eq250CentralAliasLowerConstant_mono
    {d : ℕ} {a b : ℝ} (hab : a ≤ b) :
    cmp89Eq250CentralAliasLowerConstant d a ≤
      cmp89Eq250CentralAliasLowerConstant d b := by
  have hfactor :
      0 ≤ ((2 / Real.pi) ^ d) ^ 2 * ((Real.pi / 2) ^ 2)⁻¹ :=
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (sq_nonneg _))
  rw [cmp89Eq250CentralAliasLowerConstant,
    cmp89Eq250CentralAliasLowerConstant]
  calc
    a * ((2 / Real.pi) ^ d) ^ 2 * ((Real.pi / 2) ^ 2)⁻¹ =
        a * (((2 / Real.pi) ^ d) ^ 2 * ((Real.pi / 2) ^ 2)⁻¹) := by ring
    _ ≤ b * (((2 / Real.pi) ^ d) ^ 2 * ((Real.pi / 2) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_right hab hfactor
    _ = b * ((2 / Real.pi) ^ d) ^ 2 * ((Real.pi / 2) ^ 2)⁻¹ := by ring

/-- The literal CMP89 real denominator has a lower bound independent of the
RG depth `j`: the varying source coefficient is replaced by the positive
CMP85 (2.15) floor. -/
theorem cmp85Eq215CentralAliasFloor_le_cmp89Eq250FullAliasDenominator
    {d L j : ℕ} [NeZero L] {mass a : ℝ}
    (ha : 0 < a) (hL : 1 < L) (hmass : 0 < mass)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq250CentralAliasLowerConstant d
        (cmp85Eq215SourceAveragingCoefficientFloor a (L : ℝ)) ≤
      cmp89Eq250FullAliasDenominator d L j mass
        (cmp99SourceMassParameter a (L : ℝ) j) p := by
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hfloor :=
    cmp85Eq215SourceAveragingCoefficientFloor_le_massParameter ha hLreal j
  exact (cmp89Eq250CentralAliasLowerConstant_mono hfloor).trans
    (cmp89Eq250CentralAliasLowerConstant_le_full_denominator
      (cmp99SourceMassParameter_pos ha (lt_trans zero_lt_one hLreal) j).le
      hmass hp)

end

end YangMills.RG
