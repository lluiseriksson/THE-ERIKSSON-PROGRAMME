/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.RG.KernelSchur

/-!
# Positive-semidefinite covariance kernels (gauge-RG, `hRpoly` substrate)

`docs/BALABAN-SOURCE-BOUNDS.md`.  A Gaussian field's covariance is a
**positive-semidefinite (PSD) kernel**.  This file builds the finite-lattice
PSD-covariance interface that the gauge fluctuation integral consumes,
connecting it to the exponential-decay/Schur calculus (`RG/KernelDecay.lean`,
`RG/KernelSchur.lean`):

* **`expDecay_diag_abs_le`** — the diagonal (field variance at coincident
  points) of an `ExpDecay` kernel is bounded by the amplitude `a`.
* **`IsPSDKernel`** — the covariance property `∀ u, 0 ≤ ∑_{x,y} u x K x y u y`.
* **`psd_diag_nonneg`** — the diagonal of a PSD kernel is `≥ 0` (variance ≥ 0).
* **`psd_cauchy_schwarz`** — the **covariance Cauchy–Schwarz**:
  `(∑ u K v)² ≤ (∑ u K u)(∑ v K v)` for a symmetric PSD kernel, via the
  discriminant of the nonnegative quadratic `t ↦ ∑ (u+t v) K (u+t v) ≥ 0`
  (`discrim_le_zero`).

Combined with the Schur operator-norm bound (`expDecay_op_bilinear_le`), a
background-field propagator that is a symmetric PSD `ExpDecay` kernel has: a
covariance form bounded by `a·S`, bounded variances `≤ a`, and the covariance
Cauchy–Schwarz — the full finite-lattice covariance interface a Gaussian
fluctuation bound needs.  Source-independent and volume-free.

It does NOT prove the YM activity bound (carried `hRpoly`); it is the
covariance toolkit that bound's proof consumes.  **Source.**  Elementary
PSD/Gram theory; Bałaban CMP 95–96 (the covariances it abstracts);
strategy/framing Lluis Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

variable {V : Type*}

/-- The diagonal of an exponentially-decaying kernel is bounded by the
amplitude `a` (the field variance at coincident points), when `d x x = 0`. -/
theorem expDecay_diag_abs_le {d : V → V → ℝ} {a κ : ℝ} {K : V → V → ℝ}
    (hd0 : ∀ x, d x x = 0) (hA : ExpDecay d a κ K) (x : V) :
    |K x x| ≤ a := by
  have := hA x x
  rwa [hd0 x, mul_zero, Real.exp_zero, mul_one] at this

variable [Fintype V]

/-- A finite-lattice kernel `K` is **positive semidefinite** (a covariance
kernel) if its quadratic form is nonnegative: `∀ u, 0 ≤ ∑_{x,y} u x · K x y · u y`. -/
def IsPSDKernel (K : V → V → ℝ) : Prop :=
  ∀ u : V → ℝ, 0 ≤ ∑ x, ∑ y, u x * K x y * u y

/-- The diagonal of a PSD kernel is nonnegative (`K x x ≥ 0` = variance ≥ 0):
test the quadratic form against the indicator at `x`. -/
theorem psd_diag_nonneg [DecidableEq V] {K : V → V → ℝ} (hPSD : IsPSDKernel K) (x : V) :
    0 ≤ K x x := by
  have h := hPSD (fun y => if y = x then (1 : ℝ) else 0)
  have hval : (∑ a, ∑ b, (if a = x then (1 : ℝ) else 0) * K a b * (if b = x then (1 : ℝ) else 0))
      = K x x := by
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single x]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ x) h
    · intro a _ ha
      apply Finset.sum_eq_zero; intro b _; simp [ha]
    · intro h; exact absurd (Finset.mem_univ x) h
  rwa [hval] at h

/-- **Covariance Cauchy–Schwarz** for a symmetric PSD kernel:
`(∑_{x,y} u x K x y v y)² ≤ (∑ u K u)·(∑ v K v)`.  The covariance bilinear form
satisfies the Gram/Cauchy–Schwarz inequality, via the discriminant of the
nonnegative quadratic `t ↦ ∑ (u+t v) K (u+t v) ≥ 0`. -/
theorem psd_cauchy_schwarz {K : V → V → ℝ}
    (hsymK : ∀ x y, K x y = K y x) (hPSD : IsPSDKernel K) (u v : V → ℝ) :
    (∑ x, ∑ y, u x * K x y * v y) ^ 2
      ≤ (∑ x, ∑ y, u x * K x y * u y) * (∑ x, ∑ y, v x * K x y * v y) := by
  set Buv := ∑ x, ∑ y, u x * K x y * v y with hBuv
  set Buu := ∑ x, ∑ y, u x * K x y * u y with hBuu
  set Bvv := ∑ x, ∑ y, v x * K x y * v y with hBvv
  have hBsym : (∑ x, ∑ y, v x * K x y * u y) = Buv := by
    rw [hBuv, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hsymK j i]; ring
  have hquad : ∀ t : ℝ, 0 ≤ Bvv * (t * t) + (2 * Buv) * t + Buu := by
    intro t
    have hp := hPSD (fun x => u x + t * v x)
    have hexp : (∑ x, ∑ y, (u x + t * v x) * K x y * (u y + t * v y))
        = Bvv * (t * t) + (2 * Buv) * t + Buu := by
      have hstep : (∑ x, ∑ y, (u x + t * v x) * K x y * (u y + t * v y))
          = Buu + t * Buv + t * (∑ x, ∑ y, v x * K x y * u y) + (t * t) * Bvv := by
        rw [hBuu, hBvv, hBuv]
        simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        ring
      rw [hstep, hBsym]; ring
    rw [hexp] at hp; exact hp
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

end YangMills.RG
