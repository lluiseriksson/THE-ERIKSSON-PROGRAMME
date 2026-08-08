/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251HolderPhase

/-!
# PRE-VALIDATION: alias-weight redistribution in CMP89 (2.51)

The source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the compiler.

CMP89 printed p. 586 turns the noncentral factor

`|p+l|^(alpha-1) * product_mu (1+|l_mu|)^(-1)`

into the product weight with exponent `1+(1-alpha)/d`.  This module proves
that exact redistribution for `l_mu = 2*pi*m_mu`.  The argument uses the
literal Euclidean norm already sealed for the Holder phase: every alias base
is at most three times `|p+l|_2`, and the excess exponent `1-alpha` is split
equally among the `d` coordinates.

The central alias is deliberately excluded; it is the separate `O(1)` term in
(2.51).  No complete physical integrand estimate, alias sum, analytic strip or
regional transport is claimed.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Every coordinate absolute value is bounded by the literal Euclidean norm
used in CMP89 (2.51). -/
theorem abs_le_cmp89Eq251EuclideanNorm
    {d : ℕ} (q : Fin d → ℝ) (mu : Fin d) :
    |q mu| ≤ cmp89Eq251EuclideanNorm q := by
  rw [cmp89Eq251EuclideanNorm, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  rw [cmp89Eq251MomentumSquare]
  exact Finset.single_le_sum
    (fun nu _ => sq_nonneg (q nu)) (Finset.mem_univ mu)

/-- A nonzero reciprocal alias puts the shifted Euclidean momentum outside
the radius-`pi` ball. -/
theorem pi_le_cmp89Eq251EuclideanNorm_shift
    {d : ℕ} {m : Fin d → ℤ} (hm0 : m ≠ 0)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    Real.pi ≤ cmp89Eq251EuclideanNorm
      (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) := by
  have hex : ∃ mu, m mu ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (funext h)
  obtain ⟨mu, hmu⟩ := hex
  have hmuOneInt : (1 : ℤ) ≤ |m mu| := Int.one_le_abs hmu
  have hmuOne : (1 : ℝ) ≤ |(m mu : ℝ)| := by
    exact_mod_cast hmuOneInt
  have hcoord := pi_mul_abs_cast_le_abs_add_alias (hp mu) hmu
  have hcoordNorm := abs_le_cmp89Eq251EuclideanNorm
    (fun nu => p nu + 2 * Real.pi * (m nu : ℝ)) mu
  nlinarith [Real.pi_pos]

/-- Every coordinate alias base is controlled by the same shifted Euclidean
momentum.  The explicit constant `3` includes the additive `1` in the source
weight and is uniform in the alias vector. -/
theorem one_add_abs_alias_le_three_mul_cmp89Eq251EuclideanNorm_shift
    {d : ℕ} {m : Fin d → ℤ} (hm0 : m ≠ 0)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) (mu : Fin d) :
    1 + |2 * Real.pi * (m mu : ℝ)| ≤
      3 * cmp89Eq251EuclideanNorm
        (fun nu => p nu + 2 * Real.pi * (m nu : ℝ)) := by
  let q : Fin d → ℝ := fun nu => p nu + 2 * Real.pi * (m nu : ℝ)
  have hnormPi : Real.pi ≤ cmp89Eq251EuclideanNorm q :=
    pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp
  by_cases hmu : m mu = 0
  · simp only [hmu, Int.cast_zero, mul_zero, abs_zero, add_zero]
    nlinarith [Real.pi_gt_three]
  · have hcoord := pi_mul_abs_cast_le_abs_add_alias (hp mu) hmu
    have hcoordNorm := abs_le_cmp89Eq251EuclideanNorm q mu
    have hshiftAbs :
        |2 * Real.pi * (m mu : ℝ)| =
          2 * Real.pi * |(m mu : ℝ)| := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos Real.pi_pos]
    rw [hshiftAbs]
    nlinarith [Real.pi_gt_three]

/-- The exact excess-exponent redistribution beneath the final product in
CMP89 (2.51).  It pays the explicit constant `3^(1-alpha)` once, with no
alias-cardinality factor. -/
theorem cmp89Eq251AliasExcessProduct_div_euclideanNorm_rpow_le
    {d : ℕ} (hd : 0 < d) {alpha : ℝ} (halpha1 : alpha ≤ 1)
    {m : Fin d → ℤ} (hm0 : m ≠ 0)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    (∏ mu,
        (1 + |2 * Real.pi * (m mu : ℝ)|) ^
          ((1 - alpha) / (d : ℝ))) /
        cmp89Eq251EuclideanNorm
            (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) ^
          (1 - alpha) ≤
      3 ^ (1 - alpha) := by
  let q : Fin d → ℝ := fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  let beta : ℝ := 1 - alpha
  let exponent : ℝ := beta / (d : ℝ)
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hbeta : 0 ≤ beta := by dsimp [beta]; linarith
  have hexponent : 0 ≤ exponent := div_nonneg hbeta hdReal.le
  have hnormPi : Real.pi ≤ cmp89Eq251EuclideanNorm q :=
    pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp
  have hnormPos : 0 < cmp89Eq251EuclideanNorm q :=
    Real.pi_pos.trans_le hnormPi
  have hprod :
      (∏ mu,
          (1 + |2 * Real.pi * (m mu : ℝ)|) ^ exponent) ≤
        (3 * cmp89Eq251EuclideanNorm q) ^ beta := by
    calc
      (∏ mu,
          (1 + |2 * Real.pi * (m mu : ℝ)|) ^ exponent) ≤
          ∏ _mu : Fin d, (3 * cmp89Eq251EuclideanNorm q) ^ exponent := by
        apply Finset.prod_le_prod
        · intro mu _
          positivity
        · intro mu _
          exact Real.rpow_le_rpow
            (by positivity : 0 ≤ 1 + |2 * Real.pi * (m mu : ℝ)|)
            (one_add_abs_alias_le_three_mul_cmp89Eq251EuclideanNorm_shift
              hm0 hp mu) hexponent
      _ = ((3 * cmp89Eq251EuclideanNorm q) ^ exponent) ^ d := by
        rw [Fin.prod_const]
      _ = (3 * cmp89Eq251EuclideanNorm q) ^
          (exponent * (d : ℝ)) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity : 0 ≤ 3 * cmp89Eq251EuclideanNorm q)]
      _ = (3 * cmp89Eq251EuclideanNorm q) ^ beta := by
        congr 1
        dsimp [exponent]
        field_simp
  change
    (∏ mu,
        (1 + |2 * Real.pi * (m mu : ℝ)|) ^ exponent) /
        cmp89Eq251EuclideanNorm q ^ beta ≤ 3 ^ beta
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hnormPos beta)).2
  simpa [Real.mul_rpow (show (0 : ℝ) ≤ 3 by norm_num)
    (cmp89Eq251EuclideanNorm_nonneg q)] using hprod

/-- Source-weight form of the same redistribution.  This is the literal
noncentral bridge from the radial residual in (2.51) to the already sealed
summable product weight. -/
theorem cmp89Eq251EuclideanNorm_rpow_mul_aliasWeight_le_sourceWeight
    {d : ℕ} (hd : 0 < d) {alpha : ℝ} (halpha1 : alpha ≤ 1)
    {m : Fin d → ℤ} (hm0 : m ≠ 0)
    {p : Fin d → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi) :
    cmp89Eq251EuclideanNorm
          (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) ^ (alpha - 1) *
        cmp89Eq251MultidimensionalAliasWeight 1 m ≤
      3 ^ (1 - alpha) *
        cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent d alpha) m := by
  let q : Fin d → ℝ := fun mu => p mu + 2 * Real.pi * (m mu : ℝ)
  let beta : ℝ := 1 - alpha
  let exponent : ℝ := beta / (d : ℝ)
  let extra : ℝ :=
    ∏ mu, (1 + |2 * Real.pi * (m mu : ℝ)|) ^ exponent
  have hnormPi : Real.pi ≤ cmp89Eq251EuclideanNorm q :=
    pi_le_cmp89Eq251EuclideanNorm_shift hm0 hp
  have hnormPos : 0 < cmp89Eq251EuclideanNorm q :=
    Real.pi_pos.trans_le hnormPi
  have hratio :
      extra / cmp89Eq251EuclideanNorm q ^ beta ≤ 3 ^ beta := by
    exact cmp89Eq251AliasExcessProduct_div_euclideanNorm_rpow_le
      hd halpha1 hm0 hp
  have hbasePos (mu : Fin d) :
      0 < 1 + |2 * Real.pi * (m mu : ℝ)| := by positivity
  have hextraPos : 0 < extra := by
    dsimp [extra]
    exact Finset.prod_pos fun mu _ => Real.rpow_pos_of_pos (hbasePos mu) exponent
  have hdenEq :
      (∏ mu,
          (1 + |2 * Real.pi * (m mu : ℝ)|) ^
            cmp89Eq251AliasSeriesExponent d alpha) =
        (∏ mu, (1 + |2 * Real.pi * (m mu : ℝ)|)) * extra := by
    calc
      (∏ mu,
          (1 + |2 * Real.pi * (m mu : ℝ)|) ^
            cmp89Eq251AliasSeriesExponent d alpha) =
          ∏ mu, ((1 + |2 * Real.pi * (m mu : ℝ)|) *
            (1 + |2 * Real.pi * (m mu : ℝ)|) ^ exponent) := by
        apply Finset.prod_congr rfl
        intro mu _
        rw [cmp89Eq251AliasSeriesExponent]
        change (1 + |2 * Real.pi * (m mu : ℝ)|) ^ (1 + exponent) = _
        rw [Real.rpow_add (hbasePos mu), Real.rpow_one]
      _ = (∏ mu, (1 + |2 * Real.pi * (m mu : ℝ)|)) * extra := by
        rw [Finset.prod_mul_distrib]
  have hbaseProdPos :
      0 < ∏ mu, (1 + |2 * Real.pi * (m mu : ℝ)|) :=
    Finset.prod_pos fun mu _ => hbasePos mu
  have hweightEq :
      cmp89Eq251MultidimensionalAliasWeight 1 m =
        extra * cmp89Eq251MultidimensionalAliasWeight
          (cmp89Eq251AliasSeriesExponent d alpha) m := by
    rw [cmp89Eq251MultidimensionalAliasWeight,
      cmp89Eq251MultidimensionalAliasWeight]
    simp_rw [cmp89Eq251OneDimensionalAliasWeight,
      Real.rpow_one]
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
    simp only [Finset.prod_const_one, one_div]
    rw [hdenEq]
    field_simp [ne_of_gt hbaseProdPos, ne_of_gt hextraPos]
  have hpowerEq :
      cmp89Eq251EuclideanNorm q ^ (alpha - 1) =
        1 / cmp89Eq251EuclideanNorm q ^ beta := by
    have h : alpha - 1 = -beta := by dsimp [beta]; ring
    rw [h, Real.rpow_neg hnormPos.le, one_div]
  rw [show (fun mu => p mu + 2 * Real.pi * (m mu : ℝ)) = q by rfl,
    hweightEq, hpowerEq]
  calc
    (1 / cmp89Eq251EuclideanNorm q ^ beta) *
          (extra * cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent d alpha) m) =
        (extra / cmp89Eq251EuclideanNorm q ^ beta) *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent d alpha) m := by ring
    _ ≤ 3 ^ beta *
          cmp89Eq251MultidimensionalAliasWeight
            (cmp89Eq251AliasSeriesExponent d alpha) m :=
      mul_le_mul_of_nonneg_right hratio
        (cmp89Eq251MultidimensionalAliasWeight_nonneg _ _)

end

end YangMills.RG
