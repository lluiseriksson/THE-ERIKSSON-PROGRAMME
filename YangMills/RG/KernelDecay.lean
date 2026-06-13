/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Exponential-decay kernel calculus (gauge-RG, `hRpoly` analytic substrate)

`docs/BALABAN-SOURCE-BOUNDS.md`.  Every Bałaban multiscale propagator/activity
bound rests on one analytic fact: **operator kernels with exponential spatial
decay form a calculus** — decay is preserved under sums, scalar multiples, and
(crucially) **composition**, the latter being the Combes–Thomas / Neumann-
series engine that turns a bounded-range gauge-covariant operator into an
exponentially-decaying resolvent/propagator (Bałaban CMP 95/99; the decay
constant `κ` of the YM activity bound, CMP 116 Lemma 3, is inherited from it).

This file builds that calculus abstractly and source-independently, for real
kernels on a metric space `(V, d)`:

* **`ExpDecay d a κ K`** — `|K x y| ≤ a·e^{−κ·d x y}`.
* **`expDecay_comp`** — composition: `A`, `B` decaying at rate `κ` compose to
  `(x,y) ↦ ∑_z A x z·B z y` decaying at rate `κ − σ`, amplitude `a·b·S`,
  given the uniform lattice exponential-summability `∑_z e^{−σ d(x,z)} ≤ S`
  (`0 ≤ σ ≤ κ`).  The triangle inequality extracts `e^{−(κ−σ)d(x,y)}`; the
  summability absorbs the residual `e^{−σ d(x,z)}`.  **The crux.**
* **`expDecay_add` / `expDecay_smul` / `ExpDecay.mono`** — the closure
  properties under sums, nonnegative scalars, and amplitude/rate weakening.

The summability hypothesis is exactly what the lattice animal-count /
bounded-degree machinery (`RG/AnimalTour.lean`, `RG/CubeLattice.lean`)
supplies on the `M`-cube graph.  **This is a reusable substrate; it does NOT
prove the YM activity bound** (that is the carried `hRpoly`, requiring the full
gauge fluctuation construction), but it is the analytic toolkit that bound's
proof must consume.

**Source.**  Combes–Thomas (exponential resolvent decay); Bałaban CMP 95/99
(lattice gauge propagator decay); strategy/framing Lluis Eriksson
(ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open scoped BigOperators

namespace YangMills.RG

variable {V : Type*}

/-- A real kernel `K : V → V → ℝ` has **exponential decay** with amplitude `a`
and rate `κ` relative to a distance `d`: `|K x y| ≤ a·e^{−κ·d x y}`. -/
def ExpDecay (d : V → V → ℝ) (a κ : ℝ) (K : V → V → ℝ) : Prop :=
  ∀ x y, |K x y| ≤ a * Real.exp (-κ * d x y)

/-- **Exponential decay is preserved under kernel composition** (the
Combes–Thomas / Neumann-series engine).  If `A`, `B` decay at rate `κ`, the
distance is a metric (`htri`, `hd`), and the lattice has uniform exponential
summability `∑_z e^{−σ d(x,z)} ≤ S` (`0 ≤ σ ≤ κ`), then the composed kernel
`(A∘B)(x,y) = ∑_z A x z · B z y` decays at the reduced rate `κ − σ` with
amplitude `a·b·S`.  Triangle inequality extracts `e^{−(κ−σ)d(x,y)}`; the
summability absorbs the residual `e^{−σ d(x,z)}`. -/
theorem expDecay_comp {d : V → V → ℝ} {a b κ σ S : ℝ} {A B : V → V → ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : ∀ x y, 0 ≤ d x y)
    (htri : ∀ x y z, d x y ≤ d x z + d z y)
    (hσ : 0 ≤ σ) (hσκ : σ ≤ κ)
    (hA : ExpDecay d a κ A) (hB : ExpDecay d b κ B)
    (hsum : ∀ x, Summable (fun z => Real.exp (-σ * d x z)))
    (hS : ∀ x, ∑' z, Real.exp (-σ * d x z) ≤ S) :
    ExpDecay d (a * b * S) (κ - σ) (fun x y => ∑' z, A x z * B z y) := by
  intro x y
  set C : ℝ := Real.exp (-(κ - σ) * d x y) with hC
  have hC0 : 0 ≤ C := (Real.exp_pos _).le
  have hkey : ∀ z, |A x z * B z y| ≤ (a * b * C) * Real.exp (-σ * d x z) := by
    intro z
    rw [abs_mul]
    have hprod : |A x z| * |B z y|
        ≤ (a * Real.exp (-κ * d x z)) * (b * Real.exp (-κ * d z y)) :=
      mul_le_mul (hA x z) (hB z y) (abs_nonneg _) (by positivity)
    refine le_trans hprod ?_
    have hexp : Real.exp (-κ * d x z) * Real.exp (-κ * d z y)
        ≤ C * Real.exp (-σ * d x z) := by
      rw [hC, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (htri x y z) (by linarith : (0:ℝ) ≤ κ - σ),
        mul_nonneg hσ (hd z y)]
    calc (a * Real.exp (-κ * d x z)) * (b * Real.exp (-κ * d z y))
        = (a * b) * (Real.exp (-κ * d x z) * Real.exp (-κ * d z y)) := by ring
      _ ≤ (a * b) * (C * Real.exp (-σ * d x z)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (a * b * C) * Real.exp (-σ * d x z) := by ring
  have hmaj : Summable (fun z => (a * b * C) * Real.exp (-σ * d x z)) :=
    (hsum x).mul_left _
  have hdom : Summable (fun z => |A x z * B z y|) :=
    Summable.of_nonneg_of_le (fun z => abs_nonneg _) hkey hmaj
  calc |∑' z, A x z * B z y|
      ≤ ∑' z, |A x z * B z y| := by
        have h := norm_tsum_le_tsum_norm (f := fun z => A x z * B z y)
          (by simpa [Real.norm_eq_abs] using hdom)
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' z, (a * b * C) * Real.exp (-σ * d x z) :=
        Summable.tsum_le_tsum hkey hdom hmaj
    _ = (a * b * C) * ∑' z, Real.exp (-σ * d x z) := tsum_mul_left
    _ ≤ (a * b * C) * S := mul_le_mul_of_nonneg_left (hS x) (by positivity)
    _ = (a * b * S) * Real.exp (-(κ - σ) * d x y) := by rw [hC]; ring

/-- Exponential decay is closed under **sums** (same rate, amplitudes add) —
the effective action is a sum of decaying activities. -/
theorem expDecay_add {d : V → V → ℝ} {a b κ : ℝ} {A B : V → V → ℝ}
    (hA : ExpDecay d a κ A) (hB : ExpDecay d b κ B) :
    ExpDecay d (a + b) κ (fun x y => A x y + B x y) := by
  intro x y
  calc |A x y + B x y|
      ≤ |A x y| + |B x y| := abs_add_le _ _
    _ ≤ a * Real.exp (-κ * d x y) + b * Real.exp (-κ * d x y) :=
        add_le_add (hA x y) (hB x y)
    _ = (a + b) * Real.exp (-κ * d x y) := by ring

/-- Exponential decay is closed under **nonnegative scalar multiples**. -/
theorem expDecay_smul {d : V → V → ℝ} {a κ c : ℝ} {A : V → V → ℝ}
    (hc : 0 ≤ c) (hA : ExpDecay d a κ A) :
    ExpDecay d (c * a) κ (fun x y => c * A x y) := by
  intro x y
  rw [abs_mul, abs_of_nonneg hc]
  calc c * |A x y|
      ≤ c * (a * Real.exp (-κ * d x y)) := mul_le_mul_of_nonneg_left (hA x y) hc
    _ = (c * a) * Real.exp (-κ * d x y) := by ring

/-- Decay-rate/amplitude monotonicity: a kernel decaying with amplitude `a` and
rate `κ` also decays with any larger amplitude `a'` and smaller rate `κ'`
(distances nonnegative). -/
theorem ExpDecay.mono {d : V → V → ℝ} {a a' κ κ' : ℝ} {A : V → V → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (ha : a ≤ a') (ha0 : 0 ≤ a) (hκ : κ' ≤ κ)
    (hA : ExpDecay d a κ A) : ExpDecay d a' κ' A := by
  intro x y
  refine le_trans (hA x y) ?_
  apply mul_le_mul ha _ (Real.exp_nonneg _) (le_trans ha0 ha)
  exact Real.exp_le_exp.mpr (by nlinarith [hd x y])

/-- **Asymmetric composition**: if `A` decays at the higher rate `β + σ` and `B`
at rate `β`, with summability `∑_z e^{−σ d(x,z)} ≤ S`, then `A∘B` decays at the
**unreduced** rate `β` (amplitude `a·b·S`).  The extra `σ` of `A` pays for the
intermediate summation, so the output keeps `B`'s rate — the form needed to
iterate at a fixed rate (Neumann series). -/
theorem expDecay_comp_asym {d : V → V → ℝ} {a b β σ S : ℝ} {A B : V → V → ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htri : ∀ x y z, d x y ≤ d x z + d z y)
    (hβ : 0 ≤ β)
    (hA : ExpDecay d a (β + σ) A) (hB : ExpDecay d b β B)
    (hsum : ∀ x, Summable (fun z => Real.exp (-σ * d x z)))
    (hS : ∀ x, ∑' z, Real.exp (-σ * d x z) ≤ S) :
    ExpDecay d (a * b * S) β (fun x y => ∑' z, A x z * B z y) := by
  intro x y
  set C : ℝ := Real.exp (-β * d x y) with hC
  have hkey : ∀ z, |A x z * B z y| ≤ (a * b * C) * Real.exp (-σ * d x z) := by
    intro z
    rw [abs_mul]
    have hprod : |A x z| * |B z y|
        ≤ (a * Real.exp (-(β + σ) * d x z)) * (b * Real.exp (-β * d z y)) :=
      mul_le_mul (hA x z) (hB z y) (abs_nonneg _) (by positivity)
    refine le_trans hprod ?_
    have hexp : Real.exp (-(β + σ) * d x z) * Real.exp (-β * d z y)
        ≤ C * Real.exp (-σ * d x z) := by
      rw [hC, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (htri x y z) hβ]
    calc (a * Real.exp (-(β + σ) * d x z)) * (b * Real.exp (-β * d z y))
        = (a * b) * (Real.exp (-(β + σ) * d x z) * Real.exp (-β * d z y)) := by ring
      _ ≤ (a * b) * (C * Real.exp (-σ * d x z)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (a * b * C) * Real.exp (-σ * d x z) := by ring
  have hmaj : Summable (fun z => (a * b * C) * Real.exp (-σ * d x z)) :=
    (hsum x).mul_left _
  have hdom : Summable (fun z => |A x z * B z y|) :=
    Summable.of_nonneg_of_le (fun z => abs_nonneg _) hkey hmaj
  calc |∑' z, A x z * B z y|
      ≤ ∑' z, |A x z * B z y| := by
        have h := norm_tsum_le_tsum_norm (f := fun z => A x z * B z y)
          (by simpa [Real.norm_eq_abs] using hdom)
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' z, (a * b * C) * Real.exp (-σ * d x z) :=
        Summable.tsum_le_tsum hkey hdom hmaj
    _ = (a * b * C) * ∑' z, Real.exp (-σ * d x z) := tsum_mul_left
    _ ≤ (a * b * C) * S := mul_le_mul_of_nonneg_left (hS x) (by positivity)
    _ = (a * b * S) * Real.exp (-β * d x y) := by rw [hC]; ring

/-- The `n`-fold composition (kernel power) of `K`. -/
noncomputable def Kpow (K : V → V → ℝ) : ℕ → V → V → ℝ
  | 0 => K
  | (n + 1) => fun x y => ∑' z, K x z * Kpow K n z y

/-- **Fixed-rate iterated composition** (the Neumann-series engine).  A kernel
`K` decaying at rate `κ` (amplitude `a`) has all its compositional powers
decaying at the **fixed** rate `κ − σ` with geometric amplitude `a·(a·S)ⁿ` —
the input to a resolvent/propagator decay `∑ₙ Kⁿ`.  Induction on `n` via
`expDecay_comp_asym` (`K` at rate `κ = (κ−σ)+σ` composed with `Kⁿ` at rate
`κ−σ` stays at `κ−σ`). -/
theorem expDecay_pow {d : V → V → ℝ} {a κ σ S : ℝ} {K : V → V → ℝ}
    (ha : 0 ≤ a) (hS0 : 0 ≤ S) (hd : ∀ x y, 0 ≤ d x y)
    (htri : ∀ x y z, d x y ≤ d x z + d z y)
    (hσ : 0 ≤ σ) (hσκ : σ ≤ κ)
    (hK : ExpDecay d a κ K)
    (hsum : ∀ x, Summable (fun z => Real.exp (-σ * d x z)))
    (hS : ∀ x, ∑' z, Real.exp (-σ * d x z) ≤ S) :
    ∀ n, ExpDecay d (a * (a * S) ^ n) (κ - σ) (Kpow K n) := by
  intro n
  induction n with
  | zero =>
    simp only [Kpow, pow_zero, mul_one]
    exact hK.mono hd le_rfl ha (by linarith)
  | succ n ih =>
    have hKshift : ExpDecay d a ((κ - σ) + σ) K := by
      have he : (κ - σ) + σ = κ := by ring
      rw [he]; exact hK
    have hcomp := expDecay_comp_asym (a := a) (b := a * (a * S) ^ n) (β := κ - σ)
      (σ := σ) (S := S) ha (by positivity) htri (by linarith) hKshift ih hsum hS
    have hamp : a * (a * (a * S) ^ n) * S = a * (a * S) ^ (n + 1) := by ring
    rw [hamp] at hcomp
    simpa only [Kpow] using hcomp

end YangMills.RG
