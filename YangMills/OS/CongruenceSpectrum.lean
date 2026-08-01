/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib

/-!
# What a positive weight can and cannot change

Charter: `docs/CONGRUENCE-CHARTER.md`, registered with its judges at commit
`49311bad`, **before** this file was written.  Judges run 1 (`e5d6a1b5`):
JA passed, JB failed, and the failure removed a hypothesis.

## The point of the module

The S block's coupled kernel is `T = D K D` with `D = diag(√w)` positive
diagonal.  That is a **congruence**, not a similarity.  Similarity preserves the
entire spectrum; congruence preserves much less — and much more than nothing.
This module proves both halves of that sentence, in the elementary form each
half admits.

**Rigid half.**  Definiteness, and more generally the *sign* of every quadratic
form value, is untouched by a positive-diagonal congruence (§1).  This is the
definite case of Sylvester's law of inertia (1852); the general signature-counting
law is classical and is **not** re-proved here.

**Fragile half.**  The *value* of the spectral ratio is not preserved at all, and
§2–§3 exhibit exactly how far it moves.  Restricting the tensor kernel to the two
antipodal configurations leaves a single Ising bond of coupling `β·L`
(`antipodal_block_eq_bond`), whose spectral ratio is `tanh (β·L)`
(`bond_ratio`).  **The weight fuses `L` sites into one effective site carrying
`L` times the coupling.**  Since `tanh (β·L) → 1` (§4), no bound on that ratio
can be uniform in `L`.

## What this module does NOT claim

It does not prove that the weight *attains* the antipodal restriction — that is
a limit statement, supported here only by the charter's certified numerics
(E1–E3), and it is registered as such.  It does not settle whether the S block's
gap is uniform in the extension.  It **explains** why that question is hard by
naming the exact obstruction, and explaining is not resolving.

No Gibbs measure, no infinite volume, no Yang–Mills consequence.
-/

namespace YangMills.OS

open Finset

namespace Congruence

/-! ## §1  The rigid half: congruence cannot move a sign

Everything here is about the quadratic form directly.  Working with the form
rather than with an eigenvalue count is what keeps this section elementary: a
positive diagonal is invertible, so `x ↦ D x` is a bijection of the space, and
the two forms have literally the same value set. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of `M` at `x`. -/
def quad (M : Matrix n n ℝ) (x : n → ℝ) : ℝ := ∑ i, ∑ j, x i * M i j * x j

/-- Scaling the argument by `d` is the same as congruating the matrix by `d`.
This single identity carries the whole of §1. -/
theorem quad_diagonal_congr (M : Matrix n n ℝ) (d x : n → ℝ) :
    quad (Matrix.diagonal d * M * Matrix.diagonal d) x
      = quad M (fun i => d i * x i) := by
  unfold quad
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.diagonal_apply, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

/-- If every `d i` is nonzero, scaling by `d` sends nonzero vectors to nonzero
vectors — the only place invertibility is used, and it is used essentially. -/
theorem scale_ne_zero {d x : n → ℝ} (hd : ∀ i, d i ≠ 0) (hx : x ≠ 0) :
    (fun i => d i * x i) ≠ 0 := by
  intro h
  apply hx
  funext i
  have : d i * x i = 0 := congrFun h i
  rcases mul_eq_zero.mp this with h1 | h2
  · exact absurd h1 (hd i)
  · simpa using h2

/-- **Positive definiteness is a congruence invariant.**  The definite case of
Sylvester's law of inertia, proved from the form and nothing else. -/
theorem quad_pos_congr_iff {M : Matrix n n ℝ} {d : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    (∀ x : n → ℝ, x ≠ 0 → 0 < quad (Matrix.diagonal d * M * Matrix.diagonal d) x)
      ↔ (∀ x : n → ℝ, x ≠ 0 → 0 < quad M x) := by
  constructor
  · intro h x hx
    have hinv : ∀ i, (d i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hd i)
    have := h (fun i => (d i)⁻¹ * x i) (scale_ne_zero hinv hx)
    rwa [quad_diagonal_congr, show (fun i => d i * ((d i)⁻¹ * x i)) = x from by
      funext i; field_simp] at this
  · intro h x hx
    rw [quad_diagonal_congr]
    exact h _ (scale_ne_zero hd hx)

/-- **Negative definiteness too** — so congruence cannot flip a signature even
one way.  Same proof, opposite sign. -/
theorem quad_neg_congr_iff {M : Matrix n n ℝ} {d : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    (∀ x : n → ℝ, x ≠ 0 → quad (Matrix.diagonal d * M * Matrix.diagonal d) x < 0)
      ↔ (∀ x : n → ℝ, x ≠ 0 → quad M x < 0) := by
  constructor
  · intro h x hx
    have hinv : ∀ i, (d i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hd i)
    have := h (fun i => (d i)⁻¹ * x i) (scale_ne_zero hinv hx)
    rwa [quad_diagonal_congr, show (fun i => d i * ((d i)⁻¹ * x i)) = x from by
      funext i; field_simp] at this
  · intro h x hx
    rw [quad_diagonal_congr]
    exact h _ (scale_ne_zero hd hx)

/-! ## §2  The fragile half, part one: one Ising bond

`bond a` is the transfer matrix of a single Ising bond of coupling `a`.  Its two
eigenvectors are the symmetric and antisymmetric vectors, with eigenvalues
`2 cosh a` and `2 sinh a`; their ratio is `tanh a`.  Nothing here is deep — it is
recorded because it is the exact object the weight leaves behind. -/

/-- The transfer matrix of one Ising bond of coupling `a`. -/
noncomputable def bond (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp a, Real.exp (-a); Real.exp (-a), Real.exp a]

/-- The symmetric vector is an eigenvector with eigenvalue `2 cosh a`. -/
theorem bond_mulVec_sym (a : ℝ) :
    (bond a).mulVec ![1, 1] = (2 * Real.cosh a) • ![1, 1] := by
  funext i
  fin_cases i <;>
    simp [bond, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.cosh_eq] <;> ring

/-- The antisymmetric vector is an eigenvector with eigenvalue `2 sinh a`. -/
theorem bond_mulVec_anti (a : ℝ) :
    (bond a).mulVec ![1, -1] = (2 * Real.sinh a) • ![1, -1] := by
  funext i
  fin_cases i <;>
    simp [bond, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.sinh_eq] <;> ring

/-- **The ratio of one bond.**  `2 sinh a / 2 cosh a = tanh a`. -/
theorem bond_ratio (a : ℝ) :
    (2 * Real.sinh a) / (2 * Real.cosh a) = Real.tanh a := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have h : Real.cosh a ≠ 0 := ne_of_gt (Real.cosh_pos a)
  field_simp

/-- Both eigenvalues are genuinely there: the top one is strictly positive, so
the ratio is not `0/0`. -/
theorem bond_top_pos (a : ℝ) : 0 < 2 * Real.cosh a := by
  have := Real.cosh_pos a; linarith

/-! ## §3  The fragile half, part two: the antipodal block

The kernel of `L` decoupled bonds, restricted to the two antipodal
configurations, is one bond of coupling `β · L`.  That single identity is the
mechanism: a concentrating weight does not perturb the kernel, it **restricts**
it, and the restriction to the antipodal pair carries `L` times the coupling. -/

/-- `+1` on equal spins, `-1` on opposite spins. -/
def sgn (i j : Fin 2) : ℝ := if i = j then 1 else -1

/-- The kernel of `L` decoupled bonds at coupling `β`. -/
noncomputable def tensorKernel (L : ℕ) (β : ℝ) (σ τ : Fin L → Fin 2) : ℝ :=
  Real.exp (β * ∑ j, sgn (σ j) (τ j))

/-- The all-`0` configuration. -/
def cfgPlus (L : ℕ) : Fin L → Fin 2 := fun _ => 0

/-- The all-`1` configuration. -/
def cfgMinus (L : ℕ) : Fin L → Fin 2 := fun _ => 1

theorem sgn_self (i : Fin 2) : sgn i i = 1 := by simp [sgn]

theorem sgn_zero_one : sgn 0 1 = -1 := by decide +kernel

/-- On the diagonal of the antipodal pair the kernel is `exp (β L)`. -/
theorem tensorKernel_plus_plus (L : ℕ) (β : ℝ) :
    tensorKernel L β (cfgPlus L) (cfgPlus L) = Real.exp (β * L) := by
  unfold tensorKernel cfgPlus
  simp [sgn_self]

/-- Off the diagonal it is `exp (-(β L))` — the two configurations disagree at
every one of the `L` sites. -/
theorem tensorKernel_plus_minus (L : ℕ) (β : ℝ) :
    tensorKernel L β (cfgPlus L) (cfgMinus L) = Real.exp (-(β * L)) := by
  unfold tensorKernel cfgPlus cfgMinus
  simp [sgn_zero_one]
  ring_nf

/-- **THE FUSION IDENTITY.**  The antipodal `2 × 2` block of the `L`-site kernel
is exactly one Ising bond of coupling `β · L`.  The weight does not perturb the
kernel; it restricts it, and this is what the restriction is. -/
theorem antipodal_block_eq_bond (L : ℕ) (β : ℝ) :
    !![tensorKernel L β (cfgPlus L) (cfgPlus L),
       tensorKernel L β (cfgPlus L) (cfgMinus L);
       tensorKernel L β (cfgMinus L) (cfgPlus L),
       tensorKernel L β (cfgMinus L) (cfgMinus L)] = bond (β * L) := by
  have hmm : tensorKernel L β (cfgMinus L) (cfgMinus L) = Real.exp (β * L) := by
    unfold tensorKernel cfgMinus; simp [sgn_self]
  have hmp : tensorKernel L β (cfgMinus L) (cfgPlus L) = Real.exp (-(β * L)) := by
    unfold tensorKernel cfgMinus cfgPlus
    simp [show sgn 1 0 = -1 from by decide +kernel]
    ring_nf
  rw [tensorKernel_plus_plus, tensorKernel_plus_minus, hmm, hmp]
  rfl

/-! ## §4  Why that is a wall

`tanh (β L) → 1`.  So the ratio the weight can reach exceeds every `ρ < 1` once
`L` is large enough: no bound of the form `r ≤ ρ < 1` can hold uniformly in the
extension.  Proved by hand rather than by a limit lemma, to keep the constant
visible. -/

/-- `tanh` in the exponential form used below. -/
theorem tanh_eq_exp (a : ℝ) :
    Real.tanh a = (Real.exp a - Real.exp (-a)) / (Real.exp a + Real.exp (-a)) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h : Real.exp a + Real.exp (-a) ≠ 0 := by positivity
  field_simp

/-- **The wall.**  For every coupling `β > 0` and every target `ρ < 1` there is
an extension `L` whose fused bond already beats `ρ`.  Hence `tanh (β · L)` is not
bounded away from `1`, and no `L`-uniform ratio bound survives the weight. -/
theorem exists_extension_exceeding {β : ℝ} (hβ : 0 < β) {ρ : ℝ} (hρ : ρ < 1) :
    ∃ L : ℕ, ρ < Real.tanh (β * L) := by
  rcases le_or_lt ρ 0 with hneg | hpos
  · refine ⟨1, ?_⟩
    have : 0 < Real.tanh (β * 1) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      have hs : 0 < Real.sinh (β * 1) := Real.sinh_pos_iff.mpr (by linarith)
      exact div_pos hs (Real.cosh_pos _)
    linarith
  · -- `tanh a = 1 - 2 / (exp (2a) + 1)`, so it suffices that `exp (2 β L) + 1`
    -- exceed `2 / (1 - ρ)`; the archimedean property supplies such an `L`.
    obtain ⟨L, hL⟩ := exists_nat_gt (2 / ((1 - ρ) * β))
    refine ⟨L, ?_⟩
    have hL0 : 0 < (L : ℝ) := lt_of_le_of_lt (by positivity) hL
    have hbL : 0 < β * L := by positivity
    have hlin : 2 / (1 - ρ) < β * L := by
      rw [div_lt_iff₀ (by linarith)] at hL
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 - ρ)]
      nlinarith [hL, hβ.le, hL0.le]
    -- `exp x > x` gives the exponential the room the linear bound needs
    have hexp : 2 / (1 - ρ) < Real.exp (β * L) := lt_of_lt_of_le hlin
      (Real.add_one_le_exp (β * L) |>.trans' (by linarith)).le
    have hcosh : 0 < Real.exp (β * L) + Real.exp (-(β * L)) := by positivity
    rw [tanh_eq_exp, lt_div_iff₀ hcosh]
    have hpos' : 0 < Real.exp (-(β * L)) := Real.exp_pos _
    have h1 : Real.exp (-(β * L)) = (Real.exp (β * L))⁻¹ := by
      rw [Real.exp_neg]
    have hE : 0 < Real.exp (β * L) := Real.exp_pos _
    rw [h1]
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 - ρ)] at hexp
    have := mul_pos hE hE
    nlinarith [hexp, hE, mul_pos hE hE, inv_pos.mpr hE]

/-! ## §5  Non-vacuity

The two halves are simultaneously non-trivial on one witness, which is what
makes this a statement about congruence rather than two unrelated remarks: at
`β = 1` and `L = 3` the fused bond has ratio `tanh 3`, strictly above the
unfused `tanh 1`, while §1 says no congruence whatever moved a sign. -/

/-- The fused ratio strictly exceeds the unfused one — the weight really did
move the quantity §1 says it could not move the sign of. -/
theorem fused_gt_unfused {β : ℝ} (hβ : 0 < β) {L : ℕ} (hL : 1 < L) :
    Real.tanh β < Real.tanh (β * L) := by
  have h : β < β * L := by
    have : (1 : ℝ) < L := by exact_mod_cast hL
    nlinarith
  exact Real.tanh_lt_tanh.mpr h

/-- Both eigenvalues of a fused bond are nonzero, so its ratio is a genuine
ratio and the fragile half is not about a degenerate object. -/
theorem fused_nondegenerate {a : ℝ} (ha : 0 < a) :
    0 < 2 * Real.sinh a ∧ 0 < 2 * Real.cosh a := by
  refine ⟨?_, bond_top_pos a⟩
  have := Real.sinh_pos_iff.mpr ha
  linarith

end Congruence

end YangMills.OS
