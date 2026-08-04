/-
  WronskianIdentity.lean — machine-checked core of the Wronskian identity
  ("A Wronskian Identity for Antisymmetrized Sine Sums", L. Eriksson, 2026).
  Finite form, arbitrary K. No sorry. Only Mathlib.
-/
import Mathlib

open Finset

/-- The kernel `G(m,n) = m cos(mt) sin(nt) − n sin(mt) cos(nt)`. -/
noncomputable def G (t : ℝ) (m n : ℕ) : ℝ :=
  (m : ℝ) * Real.cos (m * t) * Real.sin (n * t)
    - (n : ℝ) * Real.sin (m * t) * Real.cos (n * t)

/-- **The trigonometric collapse**: the surface bracket equals `2·G`. -/
theorem bracket_eq_two_G (t : ℝ) (m n : ℕ) :
    ((m : ℝ) - n) * Real.sin (((m : ℝ) + n) * t)
      + ((m : ℝ) + n) * Real.sin (((n : ℝ) - m) * t)
    = 2 * G t m n := by
  have h1 : ((m : ℝ) + n) * t = m * t + n * t := by ring
  have h2 : ((n : ℝ) - m) * t = n * t - m * t := by ring
  rw [h1, h2, Real.sin_add, Real.sin_sub, G]
  ring

/-- `G` is antisymmetric. -/
theorem G_antisymm (t : ℝ) (m n : ℕ) : G t n m = - G t m n := by
  unfold G; ring

/-- `G` vanishes on the diagonal. -/
theorem G_diag (t : ℝ) (m : ℕ) : G t m m = 0 := by
  unfold G; ring

/-- **The product structure**: the full double sum against `G` is the
Wronskian combination of the sine series and their derivatives. -/
theorem double_sum_eq_wronskian (K : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    ∑ m ∈ range K, ∑ n ∈ range K, a m * b n * G t m n
    = (∑ m ∈ range K, a m * (m : ℝ) * Real.cos (m * t))
        * (∑ n ∈ range K, b n * Real.sin (n * t))
      - (∑ m ∈ range K, a m * Real.sin (m * t))
        * (∑ n ∈ range K, b n * (n : ℝ) * Real.cos (n * t)) := by
  rw [sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  unfold G; ring

/-- **The antisymmetrization**: the ordered-pair sum of the
antisymmetrized coefficients against `2G` equals the full double sum. -/
theorem pair_sum_eq_double_sum (K : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n then (a m * b n - a n * b m) * (2 * G t m n) else 0)
    = 2 * ∑ m ∈ range K, ∑ n ∈ range K, a m * b n * G t m n := by
  -- split the full sum into m<n, m=n, m>n and fold the m>n part by symmetry
  have swap : ∑ m ∈ range K, ∑ n ∈ range K,
      (if n < m then a m * b n * G t m n else 0)
      = ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n then a n * b m * G t n m else 0) := by
    rw [Finset.sum_comm]
  have key : ∀ m n : ℕ,
      (if m < n then (a m * b n - a n * b m) * (2 * G t m n) else 0)
      = 2 * ((if m < n then a m * b n * G t m n else 0)
            + (if m < n then a n * b m * G t n m else 0)) := by
    intro m n
    by_cases h : m < n
    · simp only [if_pos h]; rw [G_antisymm]; ring
    · simp only [if_neg h]; ring
  have split : ∀ m n : ℕ, a m * b n * G t m n
      = (if m < n then a m * b n * G t m n else 0)
      + (if n < m then a m * b n * G t m n else 0) := by
    intro m n
    rcases lt_trichotomy m n with h | h | h
    · simp only [if_pos h, if_neg (by omega : ¬ n < m)]; ring
    · subst h; simp [G_diag]
    · simp only [if_neg (by omega : ¬ m < n), if_pos h]; ring
  calc ∑ m ∈ range K, ∑ n ∈ range K,
        (if m < n then (a m * b n - a n * b m) * (2 * G t m n) else 0)
      = ∑ m ∈ range K, ∑ n ∈ range K,
        (2 * ((if m < n then a m * b n * G t m n else 0)
              + (if m < n then a n * b m * G t n m else 0))) := by
        exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => key m n
    _ = 2 * ∑ m ∈ range K, ∑ n ∈ range K,
        ((if m < n then a m * b n * G t m n else 0)
          + (if m < n then a n * b m * G t n m else 0)) := by
        simp_rw [← Finset.mul_sum]
    _ = 2 * (∑ m ∈ range K, ∑ n ∈ range K,
          (if m < n then a m * b n * G t m n else 0)
        + ∑ m ∈ range K, ∑ n ∈ range K,
          (if m < n then a n * b m * G t n m else 0)) := by
        simp_rw [Finset.sum_add_distrib]
    _ = 2 * (∑ m ∈ range K, ∑ n ∈ range K,
          (if m < n then a m * b n * G t m n else 0)
        + ∑ m ∈ range K, ∑ n ∈ range K,
          (if n < m then a m * b n * G t m n else 0)) := by
        rw [swap]
    _ = 2 * ∑ m ∈ range K, ∑ n ∈ range K, a m * b n * G t m n := by
        congr 1
        simp_rw [← Finset.sum_add_distrib]
        exact sum_congr rfl fun m _ => sum_congr rfl fun n _ =>
          (split m n).symm

/-- **The Wronskian identity, finite form** (Theorem 1 of the note):
the antisymmetrized bracket sum over ordered pairs equals twice the
Wronskian combination. -/
theorem wronskian_identity (K : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n then (a m * b n - a n * b m)
        * (((m : ℝ) - n) * Real.sin (((m : ℝ) + n) * t)
          + ((m : ℝ) + n) * Real.sin (((n : ℝ) - m) * t)) else 0)
    = 2 * ((∑ m ∈ range K, a m * (m : ℝ) * Real.cos (m * t))
             * (∑ n ∈ range K, b n * Real.sin (n * t))
           - (∑ m ∈ range K, a m * Real.sin (m * t))
             * (∑ n ∈ range K, b n * (n : ℝ) * Real.cos (n * t))) := by
  have step : ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n then (a m * b n - a n * b m)
        * (((m : ℝ) - n) * Real.sin (((m : ℝ) + n) * t)
          + ((m : ℝ) + n) * Real.sin (((n : ℝ) - m) * t)) else 0)
      = ∑ m ∈ range K, ∑ n ∈ range K,
      (if m < n then (a m * b n - a n * b m) * (2 * G t m n) else 0) := by
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    by_cases h : m < n
    · rw [if_pos h, if_pos h, bracket_eq_two_G]
    · rw [if_neg h, if_neg h]
  rw [step, pair_sum_eq_double_sum, double_sum_eq_wronskian]

#print axioms bracket_eq_two_G
#print axioms double_sum_eq_wronskian
#print axioms pair_sum_eq_double_sum
#print axioms wronskian_identity
