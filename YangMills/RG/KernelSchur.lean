/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.KernelDecay

/-!
# Schur boundedness of exponentially-decaying kernels (gauge-RG, `hRpoly` substrate)

`docs/BALABAN-SOURCE-BOUNDS.md`.  The kernel-decay calculus (`RG/KernelDecay.lean`)
captures spatial *decay*; this file adds the **boundedness** face on a finite
lattice — the finite-dimensional Schur test — which is what a covariance /
Gaussian bound actually consumes.  An exponentially-decaying propagator kernel
therefore induces a covariance quadratic form bounded by `a·S`.

* **`expDecay_finset_row_le`** — the ℓ¹ row-sum bound `∑_y |K x y| ≤ a·S`.
* **`expDecay_quadratic_form_le`** — the Schur quadratic-form bound:
  `|∑_{x,y} u x · K x y · u y| ≤ (a·S)·∑_x (u x)²`, via the elementary Schur
  estimate `2|u_x||u_y| ≤ u_x² + u_y²` and row/column summability (the metric
  `d` symmetric).  This is exactly the shape of a covariance bound `Cov ≤ a·S`
  — so a background-field propagator with an `ExpDecay` kernel has a covariance
  form controlled by `a·S` (cf. `RG/GaussianStep.lean`, Bałaban CMP 95–96).

Source-independent and finite-dimensional (consistent with the volume-uniform
framework: the bound `a·S` is volume-free).  It does NOT prove the YM activity
bound (carried `hRpoly`); it is the boundedness toolkit that bound's proof
consumes, alongside the decay/resolvent calculus.

**Source.**  The Schur test (elementary); Bałaban CMP 95–96 (the covariance
bounds it abstracts); strategy/framing Lluis Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

variable {V : Type*} [Fintype V]

/-- **Row-sum (ℓ¹) bound** of an exponentially-decaying kernel on a finite
lattice: `∑_y |K x y| ≤ a·S` when `∑_y e^{−κ d(x,y)} ≤ S`.  The Schur-test
input and the bound on the kernel's action in sup-norm. -/
theorem expDecay_finset_row_le {d : V → V → ℝ} {a κ S : ℝ} {K : V → V → ℝ}
    (ha : 0 ≤ a) (hA : ExpDecay d a κ K)
    (hrow : ∀ x, ∑ y, Real.exp (-κ * d x y) ≤ S) (x : V) :
    ∑ y, |K x y| ≤ a * S := by
  calc ∑ y, |K x y|
      ≤ ∑ y, a * Real.exp (-κ * d x y) := Finset.sum_le_sum (fun y _ => hA x y)
    _ = a * ∑ y, Real.exp (-κ * d x y) := by rw [Finset.mul_sum]
    _ ≤ a * S := mul_le_mul_of_nonneg_left (hrow x) ha

/-- **Schur quadratic-form bound** (the covariance face of kernel decay): on a
finite lattice with symmetric metric `d`, an exponentially-decaying kernel `K`
gives a quadratic form bounded by `a·S` times the ℓ²-norm-squared:
`|∑_{x,y} u x · K x y · u y| ≤ (a·S)·∑_x (u x)²`.  The finite-dimensional Schur
test (`2|u_x||u_y| ≤ u_x²+u_y²`, then row/column summability) — the exact shape
a covariance/Gaussian bound consumes, so a propagator with `ExpDecay` kernel
has a covariance form bounded by `a·S`. -/
theorem expDecay_quadratic_form_le {d : V → V → ℝ} {a κ S : ℝ} {K : V → V → ℝ}
    (ha : 0 ≤ a) (hsym : ∀ x y, d x y = d y x) (hA : ExpDecay d a κ K)
    (hrow : ∀ x, ∑ y, Real.exp (-κ * d x y) ≤ S) (u : V → ℝ) :
    |∑ x, ∑ y, u x * K x y * u y| ≤ (a * S) * ∑ x, (u x) ^ 2 := by
  have hKrow : ∀ x, ∑ y, |K x y| ≤ a * S := expDecay_finset_row_le ha hA hrow
  have hKcol : ∀ y, ∑ x, |K x y| ≤ a * S := by
    intro y
    have hcol : ∑ x, Real.exp (-κ * d x y) ≤ S := by
      calc ∑ x, Real.exp (-κ * d x y) = ∑ x, Real.exp (-κ * d y x) := by
            apply Finset.sum_congr rfl; intro x _; rw [hsym]
        _ ≤ S := hrow y
    calc ∑ x, |K x y|
        ≤ ∑ x, a * Real.exp (-κ * d x y) := Finset.sum_le_sum (fun x _ => hA x y)
      _ = a * ∑ x, Real.exp (-κ * d x y) := by rw [Finset.mul_sum]
      _ ≤ a * S := mul_le_mul_of_nonneg_left hcol ha
  have habs : |∑ x, ∑ y, u x * K x y * u y| ≤ ∑ x, ∑ y, |u x| * |K x y| * |u y| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun x _ => ?_))
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun y _ => ?_))
    rw [abs_mul, abs_mul]
  refine le_trans habs ?_
  have hsplit : ∑ x, ∑ y, |u x| * |K x y| * |u y|
      ≤ ∑ x, ∑ y, |K x y| * (((u x) ^ 2 + (u y) ^ 2) / 2) := by
    refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
    have hamgm : |u x| * |u y| ≤ ((u x) ^ 2 + (u y) ^ 2) / 2 := by
      have h := two_mul_le_add_sq |u x| |u y|
      rw [sq_abs, sq_abs] at h
      linarith
    calc |u x| * |K x y| * |u y| = |K x y| * (|u x| * |u y|) := by ring
      _ ≤ |K x y| * (((u x) ^ 2 + (u y) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hamgm (abs_nonneg _)
  refine le_trans hsplit ?_
  have hsplit_eq : ∑ x, ∑ y, |K x y| * (((u x) ^ 2 + (u y) ^ 2) / 2)
      = (1 / 2) * ∑ x, ∑ y, |K x y| * (u x) ^ 2
        + (1 / 2) * ∑ x, ∑ y, |K x y| * (u y) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  rw [hsplit_eq]
  have hfirst : ∑ x, ∑ y, |K x y| * (u x) ^ 2 ≤ (a * S) * ∑ x, (u x) ^ 2 := by
    calc ∑ x, ∑ y, |K x y| * (u x) ^ 2
        = ∑ x, (∑ y, |K x y|) * (u x) ^ 2 := by
          refine Finset.sum_congr rfl (fun x _ => ?_); rw [Finset.sum_mul]
      _ ≤ ∑ x, (a * S) * (u x) ^ 2 :=
          Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hKrow x) (sq_nonneg _))
      _ = (a * S) * ∑ x, (u x) ^ 2 := by rw [Finset.mul_sum]
  have hsecond : ∑ x, ∑ y, |K x y| * (u y) ^ 2 ≤ (a * S) * ∑ x, (u x) ^ 2 := by
    calc ∑ x, ∑ y, |K x y| * (u y) ^ 2
        = ∑ y, (∑ x, |K x y|) * (u y) ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y _ => ?_); rw [Finset.sum_mul]
      _ ≤ ∑ y, (a * S) * (u y) ^ 2 :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hKcol y) (sq_nonneg _))
      _ = (a * S) * ∑ y, (u y) ^ 2 := by rw [Finset.mul_sum]
  linarith [hfirst, hsecond]

/-- **Operator-norm Schur bound** (the full ℓ² Schur test): on a finite lattice
with symmetric metric, an exponentially-decaying kernel `K` is bounded as a
bilinear form by `a·S·‖u‖·‖v‖`:
`|∑_{x,y} u x · K x y · v y| ≤ a·S·√(∑ u²)·√(∑ v²)`, i.e. `‖K‖_{op} ≤ a·S`.
Cauchy–Schwarz over the product index with weights `√|K x y|`
(`Finset.sum_mul_sq_le_sq_mul_sq`), then row/column summability.  The sharp
operator-norm form (the `u = v` case recovers `expDecay_quadratic_form_le`). -/
theorem expDecay_op_bilinear_le {d : V → V → ℝ} {a κ S : ℝ} {K : V → V → ℝ}
    (ha : 0 ≤ a) (hS0 : 0 ≤ S) (hsym : ∀ x y, d x y = d y x) (hA : ExpDecay d a κ K)
    (hrow : ∀ x, ∑ y, Real.exp (-κ * d x y) ≤ S) (u v : V → ℝ) :
    |∑ x, ∑ y, u x * K x y * v y|
      ≤ a * S * (Real.sqrt (∑ x, (u x) ^ 2) * Real.sqrt (∑ x, (v x) ^ 2)) := by
  have hKrow : ∀ x, ∑ y, |K x y| ≤ a * S := expDecay_finset_row_le ha hA hrow
  have hKcol : ∀ y, ∑ x, |K x y| ≤ a * S := by
    intro y
    have hcol : ∑ x, Real.exp (-κ * d x y) ≤ S := by
      calc ∑ x, Real.exp (-κ * d x y) = ∑ x, Real.exp (-κ * d y x) := by
            apply Finset.sum_congr rfl; intro x _; rw [hsym]
        _ ≤ S := hrow y
    calc ∑ x, |K x y|
        ≤ ∑ x, a * Real.exp (-κ * d x y) := Finset.sum_le_sum (fun x _ => hA x y)
      _ = a * ∑ x, Real.exp (-κ * d x y) := by rw [Finset.mul_sum]
      _ ≤ a * S := mul_le_mul_of_nonneg_left hcol ha
  set F : V × V → ℝ := fun p => Real.sqrt |K p.1 p.2| * |u p.1| with hF
  set G : V × V → ℝ := fun p => Real.sqrt |K p.1 p.2| * |v p.2| with hG
  have hFG : ∑ p : V × V, F p * G p = ∑ x, ∑ y, |u x| * |K x y| * |v y| := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    simp only [hF, hG]
    rw [show Real.sqrt |K x y| * |u x| * (Real.sqrt |K x y| * |v y|)
          = (Real.sqrt |K x y| * Real.sqrt |K x y|) * (|u x| * |v y|) by ring,
        Real.mul_self_sqrt (abs_nonneg _)]
    ring
  have hFsq : ∑ p : V × V, (F p) ^ 2 ≤ a * S * ∑ x, (u x) ^ 2 := by
    have he : ∑ p : V × V, (F p) ^ 2 = ∑ x, (∑ y, |K x y|) * (u x) ^ 2 := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [hF]
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    rw [he]
    calc ∑ x, (∑ y, |K x y|) * (u x) ^ 2
        ≤ ∑ x, (a * S) * (u x) ^ 2 :=
          Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hKrow x) (sq_nonneg _))
      _ = a * S * ∑ x, (u x) ^ 2 := by rw [Finset.mul_sum]
  have hGsq : ∑ p : V × V, (G p) ^ 2 ≤ a * S * ∑ x, (v x) ^ 2 := by
    have he : ∑ p : V × V, (G p) ^ 2 = ∑ y, (∑ x, |K x y|) * (v y) ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [hG]
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    rw [he]
    calc ∑ y, (∑ x, |K x y|) * (v y) ^ 2
        ≤ ∑ y, (a * S) * (v y) ^ 2 :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hKcol y) (sq_nonneg _))
      _ = a * S * ∑ y, (v y) ^ 2 := by rw [Finset.mul_sum]
  have hCS : (∑ p : V × V, F p * G p) ^ 2
      ≤ (∑ p : V × V, (F p) ^ 2) * (∑ p : V × V, (G p) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F G
  have hSu : 0 ≤ ∑ x, (u x) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSv : 0 ≤ ∑ x, (v x) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hX0 : 0 ≤ ∑ x, ∑ y, |u x| * |K x y| * |v y| :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => by positivity))
  have hZ0 : 0 ≤ a * S * (Real.sqrt (∑ x, (u x) ^ 2) * Real.sqrt (∑ x, (v x) ^ 2)) :=
    mul_nonneg (mul_nonneg ha hS0) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hXsq : (∑ x, ∑ y, |u x| * |K x y| * |v y|) ^ 2
      ≤ (a * S * (Real.sqrt (∑ x, (u x) ^ 2) * Real.sqrt (∑ x, (v x) ^ 2))) ^ 2 := by
    have hZsq : (a * S * (Real.sqrt (∑ x, (u x) ^ 2) * Real.sqrt (∑ x, (v x) ^ 2))) ^ 2
        = (a * S * ∑ x, (u x) ^ 2) * (a * S * ∑ x, (v x) ^ 2) := by
      rw [show (a * S * (Real.sqrt (∑ x, (u x) ^ 2) * Real.sqrt (∑ x, (v x) ^ 2))) ^ 2
            = (a * S) ^ 2 * ((Real.sqrt (∑ x, (u x) ^ 2)) ^ 2 * (Real.sqrt (∑ x, (v x) ^ 2)) ^ 2)
            by ring, Real.sq_sqrt hSu, Real.sq_sqrt hSv]
      ring
    rw [hZsq, ← hFG]
    exact le_trans hCS (mul_le_mul hFsq hGsq
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (mul_nonneg (mul_nonneg ha hS0) hSu))
  have hfin : ∑ x, ∑ y, |u x| * |K x y| * |v y|
      ≤ a * S * (Real.sqrt (∑ x, (u x) ^ 2) * Real.sqrt (∑ x, (v x) ^ 2)) := by
    have h := Real.sqrt_le_sqrt hXsq
    rwa [Real.sqrt_sq hX0, Real.sqrt_sq hZ0] at h
  refine le_trans ?_ hfin
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun x _ => ?_))
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun y _ => ?_))
  rw [abs_mul, abs_mul]

end YangMills.RG
