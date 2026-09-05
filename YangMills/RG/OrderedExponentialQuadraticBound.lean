/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.OrderedProductQuadraticBound
import YangMills.RG.NearLog

/-!
# Quadratic remainder of an ordered exponential word

This file combines the noncommutative product estimate with the explicit
Banach-algebra exponential tail.  If every generator has norm at most `r`
and `|t| r <= 1/2`, the ordered word of exponentials differs from `1` and
its literal linear insertion sum by an explicit quantity quadratic in both
`t r` and the word length.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [NormOneClass A]

/-- Ordered exponential word. -/
def orderedExpProduct (t : ℝ) (xs : List A) : A :=
  (xs.map fun x => NormedSpace.exp (t • x)).prod

/-- The tangent at the identity of an ordered exponential word is the
literal ordered-list sum of its generators.  No commutativity is used. -/
theorem hasDerivAt_orderedExpProduct_zero (xs : List A) :
    HasDerivAt (fun t : ℝ => orderedExpProduct t xs) xs.sum 0 := by
  induction xs with
  | nil =>
      simpa [orderedExpProduct] using
        (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : A)))
  | cons x xs ih =>
      have hx := hasDerivAt_exp_smul_const x (0 : ℝ)
      have hprod := hx.mul ih
      simpa [orderedExpProduct] using hprod

/-- A single exponential displacement is at most twice its linear scale on
the half unit ball. -/
theorem norm_exp_smul_sub_one_le_two_mul
    (t r : ℝ) (x : A) (hx : ‖x‖ ≤ r)
    (hsmall : |t| * r ≤ 1 / 2) :
    ‖NormedSpace.exp (t • x) - 1‖ ≤ 2 * (|t| * r) := by
  let z : ℝ := ‖t • x‖
  have hz0 : 0 ≤ z := norm_nonneg _
  have hzq : z ≤ |t| * r := by
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  have hzhalf : z ≤ 1 / 2 := hzq.trans hsmall
  have hzlt : z < 1 := by linarith
  have hden : 0 < 1 - z := by linarith
  have htail := norm_exp_sub_one_sub_self_le (Z := t • x) hzlt
  have htail2 : z ^ 2 / (1 - z) ≤ 2 * z ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg z]
  calc
    ‖NormedSpace.exp (t • x) - 1‖
        ≤ ‖NormedSpace.exp (t • x) - 1 - t • x‖ + ‖t • x‖ := by
          have h := norm_add_le
            (NormedSpace.exp (t • x) - 1 - t • x) (t • x)
          simpa only [sub_add_cancel] using h
    _ ≤ z ^ 2 / (1 - z) + z := by simpa [z] using add_le_add_right htail z
    _ ≤ 2 * z ^ 2 + z := by linarith
    _ ≤ 2 * z := by nlinarith
    _ ≤ 2 * (|t| * r) := by gcongr

/-- A single exponential has an explicit quadratic remainder at the same
uniform generator scale. -/
theorem norm_exp_smul_sub_one_sub_smul_le_two_mul_sq
    (t r : ℝ) (x : A) (hr : 0 ≤ r) (hx : ‖x‖ ≤ r)
    (hsmall : |t| * r ≤ 1 / 2) :
    ‖NormedSpace.exp (t • x) - 1 - t • x‖ ≤
      2 * (|t| * r) ^ 2 := by
  let z : ℝ := ‖t • x‖
  have hz0 : 0 ≤ z := norm_nonneg _
  have hq0 : 0 ≤ |t| * r := mul_nonneg (abs_nonneg t) hr
  have hzq : z ≤ |t| * r := by
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)
  have hzhalf : z ≤ 1 / 2 := hzq.trans hsmall
  have hzlt : z < 1 := by linarith
  have hden : 0 < 1 - z := by linarith
  have htail := norm_exp_sub_one_sub_self_le (Z := t • x) hzlt
  calc
    ‖NormedSpace.exp (t • x) - 1 - t • x‖
        ≤ z ^ 2 / (1 - z) := htail
    _ ≤ 2 * z ^ 2 := by
      rw [div_le_iff₀ hden]
      nlinarith [sq_nonneg z]
    _ ≤ 2 * (|t| * r) ^ 2 := by
      gcongr

/-- Rewrite an ordered exponential word as a product of near-identity
increments. -/
theorem orderedExpProduct_eq_orderedOnePlusProduct (t : ℝ) (xs : List A) :
    orderedExpProduct t xs =
      orderedOnePlusProduct
        (xs.map fun x => NormedSpace.exp (t • x) - 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [orderedExpProduct, List.map_cons, List.prod_cons,
        orderedOnePlusProduct_cons]
      change NormedSpace.exp (t • x) * orderedExpProduct t xs = _
      rw [ih]
      congr 1
      abel

/-- Explicit first-order displacement of an ordered exponential word. -/
theorem norm_orderedExpProduct_sub_one_le
    (t r : ℝ) (xs : List A) (hr : 0 ≤ r)
    (hx : ∀ x ∈ xs, ‖x‖ ≤ r)
    (hsmall : |t| * r ≤ 1 / 2) :
    ‖orderedExpProduct t xs - 1‖ ≤
      xs.length * (2 * (|t| * r)) *
        (1 + 2 * (|t| * r)) ^ xs.length := by
  let ys : List A := xs.map fun x => NormedSpace.exp (t • x) - 1
  have hq0 : 0 ≤ 2 * (|t| * r) := by
    positivity
  have hys : ∀ y ∈ ys, ‖y‖ ≤ 2 * (|t| * r) := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hxmem, rfl⟩
    exact norm_exp_smul_sub_one_le_two_mul t r x (hx x hxmem) hsmall
  rw [orderedExpProduct_eq_orderedOnePlusProduct]
  simpa [ys] using norm_orderedOnePlusProduct_sub_one_le ys hq0 hys

/-- The difference between the sum of exponential increments and the
literal linear insertion sum is the sum of the one-factor remainders. -/
theorem sum_exp_sub_one_sub_smul_sum (t : ℝ) (xs : List A) :
    (xs.map fun x => NormedSpace.exp (t • x) - 1).sum - t • xs.sum =
      (xs.map fun x => NormedSpace.exp (t • x) - 1 - t • x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, smul_add]
      rw [← ih]
      abel

/-- Sum of the explicit one-factor exponential remainders. -/
theorem norm_sum_exp_smul_remainder_le
    (t r : ℝ) (xs : List A) (hr : 0 ≤ r)
    (hx : ∀ x ∈ xs, ‖x‖ ≤ r)
    (hsmall : |t| * r ≤ 1 / 2) :
    ‖(xs.map fun x => NormedSpace.exp (t • x) - 1 - t • x).sum‖ ≤
      xs.length * (2 * (|t| * r) ^ 2) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hxr : ‖x‖ ≤ r := hx x (by simp)
      have htail : ∀ y ∈ xs, ‖y‖ ≤ r := by
        intro y hy
        exact hx y (by simp [hy])
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      calc
        ‖(NormedSpace.exp (t • x) - 1 - t • x) +
              (xs.map fun y =>
                NormedSpace.exp (t • y) - 1 - t • y).sum‖
            ≤ ‖NormedSpace.exp (t • x) - 1 - t • x‖ +
                ‖(xs.map fun y =>
                  NormedSpace.exp (t • y) - 1 - t • y).sum‖ :=
              norm_add_le _ _
        _ ≤ 2 * (|t| * r) ^ 2 +
              xs.length * (2 * (|t| * r) ^ 2) :=
            add_le_add
              (norm_exp_smul_sub_one_sub_smul_le_two_mul_sq
                t r x hr hxr hsmall)
              (ih htail)
        _ = ((xs.length : ℝ) + 1) *
              (2 * (|t| * r) ^ 2) := by ring

/-- Explicit second-order estimate for a complete noncommutative ordered
exponential word. -/
theorem norm_orderedExpProduct_sub_one_sub_smul_sum_le
    (t r : ℝ) (xs : List A) (hr : 0 ≤ r)
    (hx : ∀ x ∈ xs, ‖x‖ ≤ r)
    (hsmall : |t| * r ≤ 1 / 2) :
    ‖orderedExpProduct t xs - 1 - t • xs.sum‖ ≤
      (xs.length : ℝ) ^ 2 * (2 * (|t| * r)) ^ 2 *
          (1 + 2 * (|t| * r)) ^ xs.length +
        xs.length * (2 * (|t| * r) ^ 2) := by
  let ys : List A := xs.map fun x => NormedSpace.exp (t • x) - 1
  have hq0 : 0 ≤ 2 * (|t| * r) := by positivity
  have hys : ∀ y ∈ ys, ‖y‖ ≤ 2 * (|t| * r) := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hxmem, rfl⟩
    exact norm_exp_smul_sub_one_le_two_mul t r x (hx x hxmem) hsmall
  have hprod := norm_orderedOnePlusProduct_sub_one_sub_sum_le
    ys hq0 hys
  have hword : orderedExpProduct t xs = orderedOnePlusProduct ys := by
    simpa [ys] using orderedExpProduct_eq_orderedOnePlusProduct t xs
  have hlen : ys.length = xs.length := by simp [ys]
  have hsumDiff :
      ys.sum - t • xs.sum =
        (xs.map fun x => NormedSpace.exp (t • x) - 1 - t • x).sum := by
    simpa [ys] using sum_exp_sub_one_sub_smul_sum t xs
  have hsumBound :
      ‖ys.sum - t • xs.sum‖ ≤
        xs.length * (2 * (|t| * r) ^ 2) := by
    rw [hsumDiff]
    exact norm_sum_exp_smul_remainder_le t r xs hr hx hsmall
  have hdecomp :
      orderedExpProduct t xs - 1 - t • xs.sum =
        (orderedOnePlusProduct ys - 1 - ys.sum) +
          (ys.sum - t • xs.sum) := by rw [hword]; abel
  rw [hdecomp]
  calc
    ‖(orderedOnePlusProduct ys - 1 - ys.sum) +
          (ys.sum - t • xs.sum)‖
        ≤ ‖orderedOnePlusProduct ys - 1 - ys.sum‖ +
            ‖ys.sum - t • xs.sum‖ := norm_add_le _ _
    _ ≤ (ys.length : ℝ) ^ 2 * (2 * (|t| * r)) ^ 2 *
          (1 + 2 * (|t| * r)) ^ ys.length +
        xs.length * (2 * (|t| * r) ^ 2) := add_le_add hprod hsumBound
    _ = _ := by rw [hlen]

end

end YangMills.RG
