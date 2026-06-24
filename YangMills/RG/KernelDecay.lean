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

/-- **Finite-range kernels are exponentially decaying** — the operator-level
input to Combes–Thomas.  A kernel `K` supported within range `R`
(`K x y = 0` whenever `d x y > R`) and bounded by `M` decays exponentially at
*any* rate `κ ≥ 0`, with amplitude `M·e^{κR}`: on the support `e^{-κ d} ≥ e^{-κR}`
absorbs the constant, off the support `K = 0`.  Hence every finite-range lattice
operator (the nearest-neighbour Laplacian, the Wilson hopping term, the
background-field covariant difference operator) is `ExpDecay`, and — composed
through `expDecay_comp` / `expDecay_pow` — its resolvent / Green's function is too
(`expDecay_resolvent`).  This is the concrete source of the exponentially-decaying
covariance kernels that `RG/GaussianPi.lean`'s field-size bound consumes. -/
theorem finiteRange_isExpDecay {d : V → V → ℝ} {K : V → V → ℝ} {M R κ : ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hsupp : ∀ x y, R < d x y → K x y = 0)
    (hbd : ∀ x y, |K x y| ≤ M) :
    ExpDecay d (M * Real.exp (κ * R)) κ K := by
  intro x y
  by_cases h : R < d x y
  · rw [hsupp x y h, abs_zero]
    exact mul_nonneg (mul_nonneg hM (Real.exp_pos _).le) (Real.exp_pos _).le
  · push_neg at h
    have h1 : (1 : ℝ) ≤ Real.exp (κ * R) * Real.exp (-κ * d x y) := by
      rw [← Real.exp_add]
      have ht : (0 : ℝ) ≤ κ * R + -κ * d x y := by
        nlinarith [mul_nonneg hκ (by linarith : (0 : ℝ) ≤ R - d x y)]
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (κ * R + -κ * d x y) := Real.exp_le_exp.mpr ht
    calc |K x y| ≤ M := hbd x y
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * (Real.exp (κ * R) * Real.exp (-κ * d x y)) :=
            mul_le_mul_of_nonneg_left h1 hM
      _ = M * Real.exp (κ * R) * Real.exp (-κ * d x y) := by ring

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

/-- Exact finite-range propagation for kernel composition powers.

The indexing matches the repository convention `Kpow K 0 = K`: the `n`th
entry contains `n + 1` one-step kernels, so its range is `(n + 1) * R`. -/
theorem Kpow_finiteRange {d : V → V → ℝ} {K : V → V → ℝ} {R : ℝ}
    (htri : ∀ x y z, d x y ≤ d x z + d z y)
    (hK : ∀ x y, R < d x y → K x y = 0) :
    ∀ n x y, (((n + 1 : ℕ) : ℝ) * R) < d x y →
      Kpow K n x y = 0 := by
  intro n
  induction n with
  | zero =>
      intro x y hfar
      exact hK x y (by simpa using hfar)
  | succ n ih =>
      intro x y hfar
      change (∑' z, K x z * Kpow K n z y) = 0
      have hterm : ∀ z, K x z * Kpow K n z y = 0 := by
        intro z
        by_cases hxz : R < d x z
        · simp [hK x z hxz]
        · have hxz_le : d x z ≤ R := le_of_not_gt hxz
          by_cases hzy : (((n + 1 : ℕ) : ℝ) * R) < d z y
          · simp [ih z y hzy]
          · have hzy_le : d z y ≤ ((n + 1 : ℕ) : ℝ) * R :=
              le_of_not_gt hzy
            have hdist_le :
                d x y ≤ (((n + 1 + 1 : ℕ) : ℝ) * R) := by
              calc
                d x y ≤ d x z + d z y := htri x y z
                _ ≤ R + ((n + 1 : ℕ) : ℝ) * R :=
                  add_le_add hxz_le hzy_le
                _ = (((n + 1 + 1 : ℕ) : ℝ) * R) := by
                  norm_num
                  ring
            exact False.elim ((not_lt_of_ge hdist_le) hfar)
      simp [hterm]

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

/-- **Resolvent / Neumann-series decay** (the Combes–Thomas conclusion).  If a
kernel `K` decays at rate `κ` with amplitude `a`, the lattice has exponential
summability `∑_z e^{−σ d(x,z)} ≤ S`, and the smallness `a·S < 1` holds, then the
geometric series `(1 − K)⁻¹ = ∑ₙ Kⁿ` converges to a kernel decaying at the
**fixed** rate `κ − σ` with amplitude `a/(1 − a·S)`.  This is the operator-
theoretic heart of every Bałaban propagator bound: a bounded-range, small
operator has an exponentially-decaying resolvent, and the YM activity-decay
constant `κ` (CMP 116 Lemma 3) is inherited from exactly this resolvent decay
of the background-field propagator (CMP 95/99).  Sums `expDecay_pow` over the
geometric amplitudes `a·(a·S)ⁿ`. -/
theorem expDecay_resolvent {d : V → V → ℝ} {a κ σ S : ℝ} {K : V → V → ℝ}
    (ha : 0 ≤ a) (hS0 : 0 ≤ S) (haS : a * S < 1) (hd : ∀ x y, 0 ≤ d x y)
    (htri : ∀ x y z, d x y ≤ d x z + d z y)
    (hσ : 0 ≤ σ) (hσκ : σ ≤ κ)
    (hK : ExpDecay d a κ K)
    (hsum : ∀ x, Summable (fun z => Real.exp (-σ * d x z)))
    (hS : ∀ x, ∑' z, Real.exp (-σ * d x z) ≤ S) :
    ExpDecay d (a * (1 - a * S)⁻¹) (κ - σ) (fun x y => ∑' n, Kpow K n x y) := by
  have hpow := expDecay_pow ha hS0 hd htri hσ hσκ hK hsum hS
  have haS0 : 0 ≤ a * S := mul_nonneg ha hS0
  intro x y
  set E : ℝ := Real.exp (-(κ - σ) * d x y) with hE
  have hkey : ∀ n, |Kpow K n x y| ≤ (a * E) * (a * S) ^ n := by
    intro n
    calc |Kpow K n x y|
        ≤ (a * (a * S) ^ n) * E := hpow n x y
      _ = (a * E) * (a * S) ^ n := by ring
  have hgeo : Summable (fun n => (a * E) * (a * S) ^ n) :=
    (summable_geometric_of_lt_one haS0 haS).mul_left _
  have hdom : Summable (fun n => |Kpow K n x y|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hkey hgeo
  calc |∑' n, Kpow K n x y|
      ≤ ∑' n, |Kpow K n x y| := by
        have h := norm_tsum_le_tsum_norm (f := fun n => Kpow K n x y)
          (by simpa [Real.norm_eq_abs] using hdom)
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' n, (a * E) * (a * S) ^ n := Summable.tsum_le_tsum hkey hdom hgeo
    _ = (a * E) * ∑' n, (a * S) ^ n := tsum_mul_left
    _ = (a * E) * (1 - a * S)⁻¹ := by rw [tsum_geometric_of_lt_one haS0 haS]
    _ = (a * (1 - a * S)⁻¹) * Real.exp (-(κ - σ) * d x y) := by rw [hE]; ring

/-- **The resolvent of a small finite-range operator decays exponentially** — the
concrete Combes–Thomas theorem, the literal mechanism of the Bałaban propagator
bound.  A finite-range kernel `K` (range `R`, bound `M`), small enough that
`M·e^{κR}·S < 1` for some rate `κ > σ` (with `∑_z e^{−σ d(x,z)} ≤ S`), has a
Neumann-series resolvent `(1 − K)⁻¹ = ∑ₙ Kⁿ` that is `ExpDecay` at the positive
rate `κ − σ`.  Pure composition of `finiteRange_isExpDecay` (range ⇒ decay at
*any* rate) with `expDecay_resolvent` (decay + smallness ⇒ resolvent decay).
This is exactly how the YM activity-decay constant `κ` (CMP 116 Lemma 3) arises:
the background-field covariant difference operator is finite-range, and its
inverse — the propagator (CMP 95/99) — inherits exponential decay from this. -/
theorem finiteRange_resolvent_isExpDecay {d : V → V → ℝ} {K : V → V → ℝ}
    {M R κ σ S : ℝ}
    (hM : 0 ≤ M) (hS0 : 0 ≤ S) (hσ : 0 ≤ σ) (hσκ : σ ≤ κ)
    (hd : ∀ x y, 0 ≤ d x y) (htri : ∀ x y z, d x y ≤ d x z + d z y)
    (hsupp : ∀ x y, R < d x y → K x y = 0) (hbd : ∀ x y, |K x y| ≤ M)
    (hsum : ∀ x, Summable (fun z => Real.exp (-σ * d x z)))
    (hStsum : ∀ x, ∑' z, Real.exp (-σ * d x z) ≤ S)
    (hsmall : M * Real.exp (κ * R) * S < 1) :
    ExpDecay d (M * Real.exp (κ * R) * (1 - M * Real.exp (κ * R) * S)⁻¹) (κ - σ)
      (fun x y => ∑' n, Kpow K n x y) := by
  have hK : ExpDecay d (M * Real.exp (κ * R)) κ K :=
    finiteRange_isExpDecay (le_trans hσ hσκ) hM hsupp hbd
  exact expDecay_resolvent (mul_nonneg hM (Real.exp_pos _).le) hS0 hsmall hd htri hσ hσκ hK
    hsum hStsum

/-- **Volume-uniform lattice exponential summability from a shell-growth bound.**
This supplies the recurring geometric hypothesis (`∑_z e^{−σ d(x,z)} ≤ S`) of the
whole decay stack — `expDecay_comp`, `expDecay_resolvent`,
`expDecay_quadratic_form_le` — for a lattice whose graph distance from a fixed
point is the level function `ℓ`.  If the shell cardinalities `#{z : ℓ z = k}` are
bounded by `N k` and `∑ₖ N k · e^{−σk}` is summable, then
`∑_z e^{−σ·ℓ z} ≤ ∑'ₖ N k · e^{−σk}` — a bound **independent of the lattice
size** (volume-uniform).  On `ℤ^d` the shells grow polynomially
(`N k = C·(k+1)^{d−1}`), so the dominating series is a polynomial × geometric
sum, finite for every `σ > 0`; this is the geometric origin of the uniform
summability constant `S` in the Combes–Thomas / Bałaban propagator estimates.
Proof: group the sum into shells (`Finset.sum_fiberwise_of_maps_to`), bound each
shell cardinality by `N k`, and compare the finite shell-sum to the full series
(`Summable.sum_le_tsum`). -/
theorem lattice_exp_sum_le_of_shell {V : Type*} [Fintype V] [DecidableEq V]
    (ℓ : V → ℕ) {σ : ℝ} (N : ℕ → ℝ)
    (hN : ∀ k, ((Finset.univ.filter (fun z => ℓ z = k)).card : ℝ) ≤ N k)
    (hsummable : Summable (fun k => N k * Real.exp (-σ * (k : ℝ)))) :
    ∑ z, Real.exp (-σ * (ℓ z : ℝ)) ≤ ∑' k, N k * Real.exp (-σ * (k : ℝ)) := by
  classical
  set g : ℕ → ℝ := fun k => Real.exp (-σ * (k : ℝ)) with hg
  have hgnn : ∀ k, 0 ≤ g k := fun k => (Real.exp_pos _).le
  have hNnn : ∀ k, 0 ≤ N k := fun k => le_trans (Nat.cast_nonneg _) (hN k)
  have hfib : ∑ z, g (ℓ z)
      = ∑ k ∈ Finset.univ.image ℓ,
          ((Finset.univ.filter (fun z => ℓ z = k)).card : ℝ) * g k := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (t := Finset.univ.image ℓ)
      (fun z _ => Finset.mem_image_of_mem ℓ (Finset.mem_univ z)) (fun z => g (ℓ z))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hc : ∀ z ∈ Finset.univ.filter (fun z => ℓ z = k), g (ℓ z) = g k :=
      fun z hz => by rw [(Finset.mem_filter.mp hz).2]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  calc ∑ z, Real.exp (-σ * (ℓ z : ℝ))
      = ∑ k ∈ Finset.univ.image ℓ,
          ((Finset.univ.filter (fun z => ℓ z = k)).card : ℝ) * g k := hfib
    _ ≤ ∑ k ∈ Finset.univ.image ℓ, N k * g k :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hN k) (hgnn k))
    _ ≤ ∑' k, N k * g k :=
        hsummable.sum_le_tsum _ (fun k _ => mul_nonneg (hNnn k) (hgnn k))

/-- **Explicit volume-uniform summability for a bounded-degree lattice.**  When
the shells grow geometrically, `#{z : ℓ z = k} ≤ C·rᵏ` (e.g. `r =` max degree,
from the walk-count bound `card_walks_length_le_degree_pow`), and the rate beats
the growth, `r·e^{−σ} < 1` (i.e. `σ > log r`), the lattice exponential sum has the
closed-form, volume-independent bound `∑_z e^{−σ·ℓ z} ≤ C·(1 − r·e^{−σ})⁻¹`.
This is the concrete summability constant `S` that the Combes–Thomas / Bałaban
propagator estimates use: a bounded-degree lattice with a rate above its
connective constant is uniformly exponentially summable.  Specializes
`lattice_exp_sum_le_of_shell` with `N k = C·rᵏ`, summing the resulting
polynomial-free geometric series. -/
theorem lattice_exp_sum_le_geometric {V : Type*} [Fintype V] [DecidableEq V]
    (ℓ : V → ℕ) {σ C r : ℝ} (hr : 0 ≤ r)
    (hshell : ∀ k, ((Finset.univ.filter (fun z => ℓ z = k)).card : ℝ) ≤ C * r ^ k)
    (hlt : r * Real.exp (-σ) < 1) :
    ∑ z, Real.exp (-σ * (ℓ z : ℝ)) ≤ C * (1 - r * Real.exp (-σ))⁻¹ := by
  have hid : (fun (k : ℕ) => (C * r ^ k) * Real.exp (-σ * (k : ℝ)))
      = fun (k : ℕ) => C * (r * Real.exp (-σ)) ^ k := by
    funext k
    have he : Real.exp (-σ * (k : ℝ)) = (Real.exp (-σ)) ^ k := by
      rw [mul_comm, Real.exp_nat_mul]
    rw [he, mul_pow]; ring
  have hge0 : (0 : ℝ) ≤ r * Real.exp (-σ) := mul_nonneg hr (Real.exp_pos _).le
  have hsummable : Summable (fun (k : ℕ) => (C * r ^ k) * Real.exp (-σ * (k : ℝ))) := by
    rw [hid]; exact (summable_geometric_of_lt_one hge0 hlt).mul_left C
  calc ∑ z, Real.exp (-σ * (ℓ z : ℝ))
      ≤ ∑' (k : ℕ), (C * r ^ k) * Real.exp (-σ * (k : ℝ)) :=
        lattice_exp_sum_le_of_shell ℓ (fun k => C * r ^ k) hshell hsummable
    _ = C * (1 - r * Real.exp (-σ))⁻¹ := by
        rw [hid, tsum_mul_left, tsum_geometric_of_lt_one hge0 hlt]

end YangMills.RG
