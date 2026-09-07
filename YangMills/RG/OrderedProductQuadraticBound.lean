/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Normed.Algebra.Basic

/-!
# A quadratic bound for ordered noncommutative products

For a finite ordered list of perturbations `x`, this file controls

`prod (1 + x) - 1 - sum x`

without commuting any factors.  The bound is deliberately elementary and
keeps the square of the list length explicit.  It is the combinatorial
Taylor estimate needed to turn the literal contour-length budget in CMP98
(123) into an `M^2 * |A|^2` estimate.
-/

namespace YangMills.RG

open scoped BigOperators

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- Ordered product of near-identity factors. -/
def orderedOnePlusProduct (xs : List A) : A :=
  (xs.map fun x => 1 + x).prod

@[simp] theorem orderedOnePlusProduct_nil :
    orderedOnePlusProduct ([] : List A) = 1 := rfl

@[simp] theorem orderedOnePlusProduct_cons (x : A) (xs : List A) :
    orderedOnePlusProduct (x :: xs) =
      (1 + x) * orderedOnePlusProduct xs := rfl

/-- Zeroth-order product bound, valid in every normed ring. -/
theorem norm_orderedOnePlusProduct_le
    (xs : List A) {r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ x ∈ xs, ‖x‖ ≤ r) :
    ‖orderedOnePlusProduct xs‖ ≤ (1 + r) ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hxr : ‖x‖ ≤ r := hx x (by simp)
      have htail : ∀ y ∈ xs, ‖y‖ ≤ r := by
        intro y hy
        exact hx y (by simp [hy])
      calc
        ‖orderedOnePlusProduct (x :: xs)‖
            ≤ ‖1 + x‖ * ‖orderedOnePlusProduct xs‖ := norm_mul_le _ _
        _ ≤ (1 + r) * (1 + r) ^ xs.length := by
          gcongr
          · calc
              ‖1 + x‖ ≤ ‖(1 : A)‖ + ‖x‖ := norm_add_le _ _
              _ ≤ 1 + r := by simpa using add_le_add_left hxr 1
          · exact ih htail
        _ = (1 + r) ^ (x :: xs).length := by
          simp [pow_succ']

/-- First-order displacement of the ordered product.  The slightly generous
factor `(1+r)^n` makes the induction source-stable and is harmless in the
small-field regime. -/
theorem norm_orderedOnePlusProduct_sub_one_le
    (xs : List A) {r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ x ∈ xs, ‖x‖ ≤ r) :
    ‖orderedOnePlusProduct xs - 1‖ ≤
      xs.length * r * (1 + r) ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hxr : ‖x‖ ≤ r := hx x (by simp)
      have htail : ∀ y ∈ xs, ‖y‖ ≤ r := by
        intro y hy
        exact hx y (by simp [hy])
      have hprod := norm_orderedOnePlusProduct_le xs hr htail
      have hone : 1 ≤ 1 + r := by linarith
      have hpow : (1 + r) ^ xs.length ≤
          (1 + r) ^ (xs.length + 1) := by
        simpa [pow_succ] using
          mul_le_mul_of_nonneg_left hone
            (pow_nonneg (by linarith) xs.length)
      have hdecomp :
          orderedOnePlusProduct (x :: xs) - 1 =
            (orderedOnePlusProduct xs - 1) +
              x * orderedOnePlusProduct xs := by
        simp only [orderedOnePlusProduct_cons]
        noncomm_ring
      rw [hdecomp]
      calc
        ‖(orderedOnePlusProduct xs - 1) +
              x * orderedOnePlusProduct xs‖
            ≤ ‖orderedOnePlusProduct xs - 1‖ +
                ‖x * orderedOnePlusProduct xs‖ := norm_add_le _ _
        _ ≤ xs.length * r * (1 + r) ^ xs.length +
              r * (1 + r) ^ xs.length := by
          apply add_le_add (ih htail)
          exact (norm_mul_le _ _).trans
            (mul_le_mul hxr hprod (norm_nonneg _) hr)
        _ = (xs.length + 1) * r * (1 + r) ^ xs.length := by ring
        _ ≤ (xs.length + 1) * r * (1 + r) ^ (xs.length + 1) := by
          gcongr
        _ = (x :: xs).length * r *
              (1 + r) ^ (x :: xs).length := by simp

/-- Quadratic noncommutative Taylor remainder for an ordered product. -/
theorem norm_orderedOnePlusProduct_sub_one_sub_sum_le
    (xs : List A) {r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ x ∈ xs, ‖x‖ ≤ r) :
    ‖orderedOnePlusProduct xs - 1 - xs.sum‖ ≤
      (xs.length : ℝ) ^ 2 * r ^ 2 * (1 + r) ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hxr : ‖x‖ ≤ r := hx x (by simp)
      have htail : ∀ y ∈ xs, ‖y‖ ≤ r := by
        intro y hy
        exact hx y (by simp [hy])
      have hfirst := norm_orderedOnePlusProduct_sub_one_le xs hr htail
      have hone : 1 ≤ 1 + r := by linarith
      have hpow : (1 + r) ^ xs.length ≤
          (1 + r) ^ (xs.length + 1) := by
        simpa [pow_succ] using
          mul_le_mul_of_nonneg_left hone
            (pow_nonneg (by linarith) xs.length)
      have hdecomp :
          orderedOnePlusProduct (x :: xs) - 1 - (x :: xs).sum =
            (orderedOnePlusProduct xs - 1 - xs.sum) +
              x * (orderedOnePlusProduct xs - 1) := by
        simp only [orderedOnePlusProduct_cons, List.sum_cons]
        noncomm_ring
      rw [hdecomp]
      calc
        ‖(orderedOnePlusProduct xs - 1 - xs.sum) +
              x * (orderedOnePlusProduct xs - 1)‖
            ≤ ‖orderedOnePlusProduct xs - 1 - xs.sum‖ +
                ‖x * (orderedOnePlusProduct xs - 1)‖ := norm_add_le _ _
        _ ≤ (xs.length : ℝ) ^ 2 * r ^ 2 *
                (1 + r) ^ xs.length +
              r * (xs.length * r * (1 + r) ^ xs.length) := by
          apply add_le_add (ih htail)
          exact (norm_mul_le _ _).trans
            (mul_le_mul hxr hfirst (norm_nonneg _) hr)
        _ = ((xs.length : ℝ) ^ 2 + xs.length) * r ^ 2 *
              (1 + r) ^ xs.length := by ring
        _ ≤ ((xs.length + 1 : ℕ) : ℝ) ^ 2 * r ^ 2 *
              (1 + r) ^ xs.length := by
          have hn : 0 ≤ (xs.length : ℝ) := Nat.cast_nonneg _
          have hsq : (xs.length : ℝ) ^ 2 + xs.length ≤
              ((xs.length + 1 : ℕ) : ℝ) ^ 2 := by
            norm_num [Nat.cast_add, Nat.cast_one]
            nlinarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsq (sq_nonneg r))
            (pow_nonneg (by linarith) xs.length)
        _ ≤ ((xs.length + 1 : ℕ) : ℝ) ^ 2 * r ^ 2 *
              (1 + r) ^ (xs.length + 1) := by
          gcongr
        _ = ((x :: xs).length : ℝ) ^ 2 * r ^ 2 *
              (1 + r) ^ (x :: xs).length := by simp

end YangMills.RG
