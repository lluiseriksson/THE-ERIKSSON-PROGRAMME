/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib

/-!
# D-1 — the Dobrushin matrix, and where volume-freeness comes from

Charter: `docs/DOBRUSHIN-CHARTER.md`, registered with its three judges at
commit `118e32e9`, **before** this file was written.

## What this module is, and what it is not

This is **pure linear algebra over a finite index type**.  There is no
probability here, no Gibbs measure, no spin system and no physics claim.  A
single nonnegative matrix `C`, supported on pairs at distance at most one and
with row sums at most `α < 1`, has its resolvent series `∑ₙ Cⁿ` bounded entrywise
by `α ^ dist / (1 - α)`.

That bound is the entire reason a Dobrushin argument is **free of the volume**:
the index type `ι` may be as large as one likes, and neither `α` nor the
exponent mentions its cardinality.  Every constant in sight is read off the
single-site data.

The S block's uniform theorems are proved by Schur's test on **constant row
sums** (`SpatialUniform.lean`), and `coupled_rowSums_not_constant`
(`SpatialExtent.lean`) shows those row sums stop being constant the moment the
spatial weight is switched on.  The hypothesis below asks only for row sums
**bounded** by `α`, never constant — which is precisely the crack the coupled
kernel falls through.

## The mechanism, in one line

`Cⁿ i j` vanishes unless `n ≥ dist i j`, because a path of `n` steps of range one
cannot cross a larger distance; and it is at most `αⁿ`, because row sums
multiply.  Summing the surviving tail is a geometric series.

## What is proved

* `Matrix.pow_apply_nonneg` — nonnegativity survives powers.
* `Matrix.pow_rowSum_le` — `∑ⱼ (Cⁿ) i j ≤ αⁿ`.
* `Matrix.pow_apply_eq_zero_of_lt_dist` — the support statement: `n < dist i j`
  forces `(Cⁿ) i j = 0`.  This is the only place the triangle inequality is used.
* `Matrix.sum_range_pow_apply_le` — the partial sums, bounded **uniformly in the
  number of terms**.
* `Matrix.tsum_pow_apply_le` — hence the series itself.

`dist` is an abstract `ℕ`-valued function with a triangle inequality and
`dist i i = 0`; graph distance on any locally finite graph is an instance, and
nothing below needs symmetry.
-/

namespace YangMills.OS

open Finset

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1  Nonnegativity survives powers -/

/-- Powers of an entrywise nonnegative matrix are entrywise nonnegative. -/
theorem pow_apply_nonneg {C : Matrix ι ι ℝ} (hC : ∀ i j, 0 ≤ C i j) :
    ∀ (n : ℕ) (i j : ι), 0 ≤ (C ^ n) i j := by
  intro n
  induction n with
  | zero =>
      intro i j
      simp only [pow_zero, Matrix.one_apply]
      split <;> norm_num
  | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hC k j)

/-! ## §2  Row sums multiply

This is the step that never sees the size of `ι`. -/

/-- **Row sums multiply.**  If every row of `C` sums to at most `α`, every row of
`Cⁿ` sums to at most `αⁿ` — with no dependence on `Fintype.card ι`. -/
theorem pow_rowSum_le {C : Matrix ι ι ℝ} {α : ℝ}
    (hC : ∀ i j, 0 ≤ C i j) (hα0 : 0 ≤ α) (hrow : ∀ i, ∑ j, C i j ≤ α) :
    ∀ (n : ℕ) (i : ι), ∑ j, (C ^ n) i j ≤ α ^ n := by
  intro n
  induction n with
  | zero =>
      intro i
      simp [Matrix.one_apply]
  | succ n ih =>
      intro i
      have hexpand : ∑ j, (C ^ (n + 1)) i j
          = ∑ k, (C ^ n) i k * ∑ j, C k j := by
        simp only [pow_succ, Matrix.mul_apply]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
      rw [hexpand]
      have hstep : ∑ k, (C ^ n) i k * ∑ j, C k j ≤ ∑ k, (C ^ n) i k * α :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hrow k) (pow_apply_nonneg hC n i k)
      refine hstep.trans ?_
      rw [← Finset.sum_mul, pow_succ]
      exact mul_le_mul_of_nonneg_right (ih i) hα0

/-- An entry is bounded by its row sum, hence by `αⁿ`. -/
theorem pow_apply_le {C : Matrix ι ι ℝ} {α : ℝ}
    (hC : ∀ i j, 0 ≤ C i j) (hα0 : 0 ≤ α) (hrow : ∀ i, ∑ j, C i j ≤ α)
    (n : ℕ) (i j : ι) : (C ^ n) i j ≤ α ^ n := by
  refine le_trans ?_ (pow_rowSum_le hC hα0 hrow n i)
  exact Finset.single_le_sum (f := fun j => (C ^ n) i j)
    (fun k _ => pow_apply_nonneg hC n i k) (Finset.mem_univ j)

/-! ## §3  The support of a power

A walk of `n` steps, each of range at most one, cannot reach further than `n`. -/

/-- **The support statement.**  If `C` is supported on pairs at distance at most
one, then `(Cⁿ) i j` vanishes whenever `n < dist i j`.  This is the only lemma
that uses the triangle inequality. -/
theorem pow_apply_eq_zero_of_lt_dist {C : Matrix ι ι ℝ} {d : ι → ι → ℕ}
    (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hsupp : ∀ i j, 1 < d i j → C i j = 0) :
    ∀ (n : ℕ) (i j : ι), n < d i j → (C ^ n) i j = 0 := by
  intro n
  induction n with
  | zero =>
      intro i j hij
      have hne : i ≠ j := by
        rintro rfl
        rw [hself i] at hij
        exact absurd hij (lt_irrefl 0)
      simp [pow_zero, hne]
  | succ n ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hik : n < d i k
      · rw [ih i k hik, zero_mul]
      · have hik' : d i k ≤ n := Nat.not_lt.mp hik
        have hchain : d i j ≤ n + d k j := le_trans (htri i k j) (by omega)
        have : 1 < d k j := by omega
        rw [hsupp k j this, mul_zero]

/-! ## §4  The resolvent bound -/

/-- A finite geometric sum is bounded by the limit of the series. -/
private theorem geom_partial_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (k : ℕ) :
    ∑ m ∈ Finset.range k, α ^ m ≤ (1 - α)⁻¹ := by
  have hsum : Summable (fun m : ℕ => α ^ m) := summable_geometric_of_lt_one hα0 hα1
  calc ∑ m ∈ Finset.range k, α ^ m
      ≤ ∑' m : ℕ, α ^ m :=
        Summable.sum_le_tsum _ (fun _ _ => pow_nonneg hα0 _) hsum
    _ = (1 - α)⁻¹ := tsum_geometric_of_lt_one hα0 hα1

/-- **D-1.**  The partial sums of the resolvent series are bounded entrywise by
`α ^ dist i j / (1 - α)`, **uniformly in the number of terms** and with no
reference whatever to the size of the index type.

This is the volume-free estimate the whole lane rests on.  Note the row-sum
hypothesis: `∑ j, C i j ≤ α`, never `= α`. -/
theorem sum_range_pow_apply_le {C : Matrix ι ι ℝ} {d : ι → ι → ℕ} {α : ℝ}
    (hC : ∀ i j, 0 ≤ C i j) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ j, C i j ≤ α)
    (hself : ∀ i, d i i = 0) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hsupp : ∀ i j, 1 < d i j → C i j = 0) (i j : ι) (N : ℕ) :
    ∑ n ∈ Finset.range N, (C ^ n) i j ≤ α ^ (d i j) / (1 - α) := by
  have hpos : (0 : ℝ) < 1 - α := by linarith
  -- every term is dominated by the truncated geometric one
  have hterm : ∀ n ∈ Finset.range N,
      (C ^ n) i j ≤ (if d i j ≤ n then α ^ n else 0) := by
    intro n _
    by_cases hn : d i j ≤ n
    · simp only [hn, if_true]
      exact pow_apply_le hC hα0 hrow n i j
    · simp only [hn, if_false]
      exact le_of_eq
        (pow_apply_eq_zero_of_lt_dist hself htri hsupp n i j (Nat.not_le.mp hn))
  refine le_trans (Finset.sum_le_sum hterm) ?_
  by_cases hN : N ≤ d i j
  · -- no term has survived at all
    have hzero : ∑ n ∈ Finset.range N, (if d i j ≤ n then α ^ n else 0) = 0 :=
      Finset.sum_eq_zero fun n hn => by
        rw [if_neg (Nat.not_le.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) hN))]
    rw [hzero]
    exact div_nonneg (pow_nonneg hα0 _) hpos.le
  · -- split at `d i j` and reindex the surviving block by `n = d i j + k`
    push_neg at hN
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (d i j)) hN.le]
    have h1 : ∑ n ∈ Finset.Ico 0 (d i j), (if d i j ≤ n then α ^ n else 0) = 0 :=
      Finset.sum_eq_zero fun n hn => by
        rw [if_neg (Nat.not_le.mpr (Finset.mem_Ico.mp hn).2)]
    have h2 : ∑ n ∈ Finset.Ico (d i j) N, (if d i j ≤ n then α ^ n else 0)
        = ∑ n ∈ Finset.Ico (d i j) N, α ^ n :=
      Finset.sum_congr rfl fun n hn => by
        rw [if_pos (Finset.mem_Ico.mp hn).1]
    rw [h1, h2, zero_add, Finset.sum_Ico_eq_sum_range]
    simp only [pow_add]
    rw [← Finset.mul_sum, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (geom_partial_le hα0 hα1 _) (pow_nonneg hα0 _)

/-- **D-1, series form.**  The resolvent series itself obeys the same bound. -/
theorem tsum_pow_apply_le {C : Matrix ι ι ℝ} {d : ι → ι → ℕ} {α : ℝ}
    (hC : ∀ i j, 0 ≤ C i j) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ j, C i j ≤ α)
    (hself : ∀ i, d i i = 0) (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hsupp : ∀ i j, 1 < d i j → C i j = 0) (i j : ι) :
    ∑' n : ℕ, (C ^ n) i j ≤ α ^ (d i j) / (1 - α) :=
  Real.tsum_le_of_sum_range_le (fun n => pow_apply_nonneg hC n i j)
    (fun N => sum_range_pow_apply_le hC hα0 hα1 hrow hself htri hsupp i j N)

/-! ## §5  Non-vacuity

The hypotheses of D-1 are not jointly vacuous, and the conclusion is not the
degenerate `dist = 0` case.  A three-point chain carries `1/4` on every pair at
distance at most one; its row sums are bounded by `α = 3/4 < 1`, its endpoints
are genuinely two apart, and the matrix is not zero. -/

/-- Graph distance on a three-point chain. -/
def witnessD (i j : Fin 3) : ℕ := (i.val - j.val) + (j.val - i.val)

/-- `1/4` on every pair at distance at most one, `0` beyond. -/
noncomputable def witnessC : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if witnessD i j ≤ 1 then (1 / 4 : ℝ) else 0

theorem witnessD_self (i : Fin 3) : witnessD i i = 0 := by
  simp [witnessD]

theorem witnessD_triangle (i j k : Fin 3) :
    witnessD i k ≤ witnessD i j + witnessD j k := by
  simp only [witnessD]; omega

theorem witnessC_nonneg (i j : Fin 3) : 0 ≤ witnessC i j := by
  unfold witnessC; split <;> norm_num

theorem witnessC_supp (i j : Fin 3) (h : 1 < witnessD i j) : witnessC i j = 0 := by
  unfold witnessC; rw [if_neg (Nat.not_le.mpr h)]

theorem witnessC_rowSum (i : Fin 3) : ∑ j, witnessC i j ≤ (3 / 4 : ℝ) := by
  fin_cases i <;> norm_num [witnessC, witnessD, Fin.sum_univ_three]

/-- The endpoints really are two apart, so the exponent below is not `0`. -/
theorem witnessD_endpoints : witnessD 0 2 = 2 := by decide

/-- The matrix is not the zero matrix, so the support hypothesis is not met by
collapsing everything. -/
theorem witnessC_ne_zero : witnessC 0 0 ≠ 0 := by
  norm_num [witnessC, witnessD]

/-- **Non-vacuity witness.**  D-1 applies to this data and says something: the
entire resolvent series between the two ends of the chain is at most `9/4`,
however many terms are taken. -/
theorem witness_bound (N : ℕ) :
    ∑ n ∈ Finset.range N, (witnessC ^ n) 0 2 ≤ (3 / 4 : ℝ) ^ (2 : ℕ) / (1 - 3 / 4) := by
  have h := sum_range_pow_apply_le (C := witnessC) (d := witnessD) (α := 3 / 4)
    witnessC_nonneg (by norm_num) (by norm_num) witnessC_rowSum
    witnessD_self witnessD_triangle witnessC_supp 0 2 N
  rwa [witnessD_endpoints] at h

end Matrix

end YangMills.OS
