/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251MultidimensionalAliasProduct

/-!
# PRE-VALIDATION: signed-lattice `l1` exponential sum

This source is present, its `.olean` has not yet been materialized, and its
result has not yet been verified by the compiler.

The signed endpoint contour below CMP89 (2.51) produces the literal decay
`exp (-delta * sum_mu |u_mu|)` for an integer lattice displacement `u`.  This
module keeps that `l1` geometry instead of replacing it by a ball-counting
majorant.  It evaluates the one-dimensional integer series exactly and
factorizes every finite centered product box, giving the uniform bound

`((1 + exp (-delta)) / (1 - exp (-delta))) ^ d`.

The result is a finite-box bound, which is the form needed before passing to
the finite physical owner set.  It does not yet identify the physical owner
displacement with this integer box, bound the complete stabilized integrand,
construct `B0`, or attain window 15.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- One coordinate of the signed-contour spatial decay. -/
def cmp89SignedLatticeOneDimensionalExpWeight
    (delta : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-delta * (n.natAbs : ℝ))

/-- The coordinate exponential weight is nonnegative. -/
theorem cmp89SignedLatticeOneDimensionalExpWeight_nonneg
    (delta : ℝ) (n : ℤ) :
    0 ≤ cmp89SignedLatticeOneDimensionalExpWeight delta n := by
  rw [cmp89SignedLatticeOneDimensionalExpWeight]
  positivity

/-- Positive decay makes the coordinate weight summable on all of `Int`. -/
theorem summable_cmp89SignedLatticeOneDimensionalExpWeight
    {delta : ℝ} (hdelta : 0 < delta) :
    Summable (cmp89SignedLatticeOneDimensionalExpWeight delta) := by
  let q : ℝ := Real.exp (-delta)
  have hqNonneg : 0 ≤ q := Real.exp_pos (-delta) |>.le
  have hqLt : q < 1 := by
    rw [q, Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hqNonneg hqLt
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa [cmp89SignedLatticeOneDimensionalExpWeight, q,
      ← Real.exp_nat_mul, mul_comm] using hgeom
  · simpa [cmp89SignedLatticeOneDimensionalExpWeight, q,
      ← Real.exp_nat_mul, mul_comm] using hgeom

/-- Exact geometric evaluation of the spatial exponential series on `Int`.
This is the one-dimensional input to the `l1` product bound. -/
theorem tsum_cmp89SignedLatticeOneDimensionalExpWeight
    {delta : ℝ} (hdelta : 0 < delta) :
    (∑' n : ℤ, cmp89SignedLatticeOneDimensionalExpWeight delta n) =
      (1 + Real.exp (-delta)) / (1 - Real.exp (-delta)) := by
  let q : ℝ := Real.exp (-delta)
  have hqNonneg : 0 ≤ q := Real.exp_pos (-delta) |>.le
  have hqLt : q < 1 := by
    rw [q, Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hqNonneg hqLt
  have hnat :
      Summable (fun n : ℕ =>
        cmp89SignedLatticeOneDimensionalExpWeight delta (n : ℤ)) := by
    simpa [cmp89SignedLatticeOneDimensionalExpWeight, q,
      ← Real.exp_nat_mul, mul_comm] using hgeom
  have hneg :
      Summable (fun n : ℕ =>
        cmp89SignedLatticeOneDimensionalExpWeight delta (-(n + 1 : ℕ) : ℤ)) := by
    simpa [cmp89SignedLatticeOneDimensionalExpWeight, q,
      ← Real.exp_nat_mul, mul_comm] using hgeom.comp_injective Nat.succ_injective
  rw [tsum_of_nat_of_neg_add_one hnat hneg]
  have hnatTsum :
      (∑' n : ℕ,
        cmp89SignedLatticeOneDimensionalExpWeight delta (n : ℤ)) =
        (1 - q)⁻¹ := by
    simpa [cmp89SignedLatticeOneDimensionalExpWeight, q,
      ← Real.exp_nat_mul, mul_comm] using
      tsum_geometric_of_lt_one hqNonneg hqLt
  have hnegTsum :
      (∑' n : ℕ,
        cmp89SignedLatticeOneDimensionalExpWeight delta (-(n + 1 : ℕ) : ℤ)) =
        q * (1 - q)⁻¹ := by
    calc
      (∑' n : ℕ,
          cmp89SignedLatticeOneDimensionalExpWeight delta (-(n + 1 : ℕ) : ℤ)) =
          ∑' n : ℕ, q ^ (n + 1) := by
            apply tsum_congr
            intro n
            simp [cmp89SignedLatticeOneDimensionalExpWeight, q,
              ← Real.exp_nat_mul, mul_comm]
      _ = ∑' n : ℕ, q * q ^ n := by
            apply tsum_congr
            intro n
            rw [pow_succ']
      _ = q * ∑' n : ℕ, q ^ n := tsum_mul_left
      _ = q * (1 - q)⁻¹ := by
            rw [tsum_geometric_of_lt_one hqNonneg hqLt]
  rw [hnatTsum, hnegTsum]
  change (1 - q)⁻¹ + q * (1 - q)⁻¹ = (1 + q) / (1 - q)
  rw [div_eq_mul_inv]
  ring

/-- Literal `l1` product weight for an integer displacement in `d`
coordinates. -/
def cmp89SignedLatticeL1ExponentialWeight
    {d : ℕ} (delta : ℝ) (u : Fin d → ℤ) : ℝ :=
  ∏ mu, cmp89SignedLatticeOneDimensionalExpWeight delta (u mu)

/-- The product representation is exactly the signed-contour `l1` decay. -/
theorem cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs
    {d : ℕ} (delta : ℝ) (u : Fin d → ℤ) :
    cmp89SignedLatticeL1ExponentialWeight delta u =
      Real.exp (-delta * ∑ mu, ((u mu).natAbs : ℝ)) := by
  rw [cmp89SignedLatticeL1ExponentialWeight]
  simp only [cmp89SignedLatticeOneDimensionalExpWeight, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- The finite centered displacement-box sum of the literal `l1` weight. -/
def cmp89SignedLatticeCenteredL1ExponentialSum
    (d N : ℕ) (delta : ℝ) : ℝ :=
  ∑ u ∈ cmp89Eq245CenteredAliasVectors d N,
    cmp89SignedLatticeL1ExponentialWeight delta u

/-- Exact factorization of every finite centered displacement box. -/
theorem cmp89SignedLatticeCenteredL1ExponentialSum_eq_pow
    (d N : ℕ) (delta : ℝ) :
    cmp89SignedLatticeCenteredL1ExponentialSum d N delta =
      (∑ n ∈ cmp89Eq245CenteredAliasIntegers N,
        cmp89SignedLatticeOneDimensionalExpWeight delta n) ^ d := by
  simp only [cmp89SignedLatticeCenteredL1ExponentialSum,
    cmp89Eq245CenteredAliasVectors,
    cmp89SignedLatticeL1ExponentialWeight]
  rw [Finset.sum_prod_piFinset]
  simp

/-- Uniform finite-box bound with the exact geometric constant.  In dimension
`d`, this retains the `delta ^ (-d)` scale of the signed `l1` decay rather
than paying a ball-counting power `delta ^ (-(d+1))`. -/
theorem cmp89SignedLatticeCenteredL1ExponentialSum_le_geometric_pow
    (d N : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    cmp89SignedLatticeCenteredL1ExponentialSum d N delta ≤
      ((1 + Real.exp (-delta)) / (1 - Real.exp (-delta))) ^ d := by
  rw [cmp89SignedLatticeCenteredL1ExponentialSum_eq_pow]
  have hfiniteNonneg :
      0 ≤ ∑ n ∈ cmp89Eq245CenteredAliasIntegers N,
        cmp89SignedLatticeOneDimensionalExpWeight delta n := by
    exact Finset.sum_nonneg fun n _ =>
      cmp89SignedLatticeOneDimensionalExpWeight_nonneg delta n
  have hfiniteLe :
      (∑ n ∈ cmp89Eq245CenteredAliasIntegers N,
          cmp89SignedLatticeOneDimensionalExpWeight delta n) ≤
        ∑' n : ℤ, cmp89SignedLatticeOneDimensionalExpWeight delta n := by
    exact (summable_cmp89SignedLatticeOneDimensionalExpWeight hdelta).sum_le_tsum
      (cmp89Eq245CenteredAliasIntegers N)
      (fun n _ => cmp89SignedLatticeOneDimensionalExpWeight_nonneg delta n)
  refine (pow_le_pow_left₀ hfiniteNonneg hfiniteLe d).trans_eq ?_
  rw [tsum_cmp89SignedLatticeOneDimensionalExpWeight hdelta]

end

end YangMills.RG
