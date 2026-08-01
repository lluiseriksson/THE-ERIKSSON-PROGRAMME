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
  -- the product associates as `(diagonal d * M) * diagonal d`, so peel the
  -- right factor first and the left one second
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

omit [Fintype n] [DecidableEq n] in
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
      funext i; rw [← mul_assoc, mul_inv_cancel₀ (hd i), one_mul]] at this
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
      funext i; rw [← mul_assoc, mul_inv_cancel₀ (hd i), one_mul]] at this
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

/-! ### The sign hypothesis `bond_ratio` needs, and why

`bond_ratio` is an ALGEBRAIC identity: `2 sinh a / 2 cosh a = tanh a` for every
real `a`.  The companion paper reads it as the *subdominant modulus* ratio
`max{|λ| : λ ≠ ρ}/ρ`, and those two agree only when `2 sinh a ≥ 0`, i.e. when
`a ≥ 0`.  For `a < 0` the antisymmetric eigenvalue is negative and the modulus
ratio is `|tanh a|`, not `tanh a`.

Recorded because an earlier draft of the paper stated the lemma without the sign
hypothesis, and the Lean identity did not catch it: the identity was true, the
sentence built on it was not.  The consumer uses `a = β·L` with `β > 0`, so the
hypothesis costs nothing. -/

/-- For `a ≥ 0` the antisymmetric eigenvalue is nonnegative, so the algebraic
identity of `bond_ratio` really is the modulus ratio. -/
theorem bond_sinh_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ 2 * Real.sinh a := by
  rcases lt_or_eq_of_le ha with h | h
  · have := Real.sinh_pos_iff.mpr h; linarith
  · rw [← h, Real.sinh_zero]; norm_num

/-- And the hypothesis is not vacuous: for `a < 0` the quantity `bond_ratio`
computes is strictly negative, hence cannot be a ratio of moduli. -/
theorem bond_ratio_neg_of_neg {a : ℝ} (ha : a < 0) :
    (2 * Real.sinh a) / (2 * Real.cosh a) < 0 := by
  have hpos : 0 < Real.sinh (-a) := Real.sinh_pos_iff.mpr (by linarith)
  rw [Real.sinh_neg] at hpos
  have hc : 0 < Real.cosh a := Real.cosh_pos a
  apply div_neg_of_neg_of_pos <;> linarith

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

/-- `decide` cannot do this: `sgn` lands in `ℝ`, whose equality is not
constructively decidable, so the decision procedure gets stuck on
`Classical.choice`.  The index comparison IS decidable, so discharge that and
let `if_neg` do the rest. -/
theorem sgn_zero_one : sgn 0 1 = -1 := by
  unfold sgn
  rw [if_neg (by decide : ¬((0 : Fin 2) = 1))]

theorem sgn_one_zero : sgn 1 0 = -1 := by
  unfold sgn
  rw [if_neg (by decide : ¬((1 : Fin 2) = 0))]

/-- On the diagonal of the antipodal pair the kernel is `exp (β L)`. -/
theorem tensorKernel_plus_plus (L : ℕ) (β : ℝ) :
    tensorKernel L β (cfgPlus L) (cfgPlus L) = Real.exp (β * L) := by
  unfold tensorKernel cfgPlus
  simp [sgn_self]

/-- Off the diagonal it is `exp (-(β L))` — the two configurations disagree at
every one of the `L` sites. -/
theorem tensorKernel_plus_minus (L : ℕ) (β : ℝ) :
    tensorKernel L β (cfgPlus L) (cfgMinus L) = Real.exp (-(β * L)) := by
  have hs : ∑ _j : Fin L, sgn (cfgPlus L _j) (cfgMinus L _j) = -(L : ℝ) := by
    simp [cfgPlus, cfgMinus, sgn_zero_one]
  unfold tensorKernel
  rw [hs, show β * (-(L : ℝ)) = -(β * L) from by ring]

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
    have hs : ∑ _j : Fin L, sgn (cfgMinus L _j) (cfgPlus L _j) = -(L : ℝ) := by
      simp [cfgPlus, cfgMinus, sgn_one_zero]
    unfold tensorKernel
    rw [hs, show β * (-(L : ℝ)) = -(β * L) from by ring]
  rw [tensorKernel_plus_plus, tensorKernel_plus_minus, hmm, hmp]
  rfl

/-! ## §4  Why that is a wall

`tanh (β L) → 1`.  So the ratio the weight can reach exceeds every `ρ < 1` once
`L` is large enough: no bound of the form `r ≤ ρ < 1` can hold uniformly in the
extension.  Proved by hand rather than by a limit lemma, to keep the constant
visible. -/

/-- **The explicit approach rate.**  `1 - tanh x ≤ e^{-x}`, because
`1 - tanh x = e^{-x} / cosh x` and `cosh ≥ 1`.  Stated as a bound rather than as
a limit so the constant stays visible, and because the pinned Mathlib has no
monotonicity lemma for `tanh` to lean on. -/
theorem one_sub_tanh_le (x : ℝ) : 1 - Real.tanh x ≤ Real.exp (-x) := by
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have hc' : Real.cosh x ≠ 0 := ne_of_gt hc
  have h1 : (1 : ℝ) ≤ Real.cosh x := Real.one_le_cosh x
  have key : 1 - Real.tanh x = Real.exp (-x) / Real.cosh x := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.cosh_eq, Real.sinh_eq]
    have hne : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
    field_simp
    ring
  rw [key]
  exact div_le_self (Real.exp_pos _).le h1

/-- Strict monotonicity of `tanh`, proved here because the pin does not carry
it: `tanh b - tanh a = sinh (b - a) / (cosh a cosh b)`. -/
theorem tanh_lt_tanh_of_lt {a b : ℝ} (h : a < b) : Real.tanh a < Real.tanh b := by
  have ha : 0 < Real.cosh a := Real.cosh_pos a
  have hb : 0 < Real.cosh b := Real.cosh_pos b
  have ha' : Real.cosh a ≠ 0 := ne_of_gt ha
  have hb' : Real.cosh b ≠ 0 := ne_of_gt hb
  have hs : 0 < Real.sinh b * Real.cosh a - Real.cosh b * Real.sinh a := by
    have hpos := Real.sinh_pos_iff.mpr (show (0 : ℝ) < b - a by linarith)
    rwa [Real.sinh_sub] at hpos
  have key : Real.tanh b - Real.tanh a
      = (Real.sinh b * Real.cosh a - Real.cosh b * Real.sinh a)
        / (Real.cosh a * Real.cosh b) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have : 0 < Real.tanh b - Real.tanh a := by
    rw [key]; exact div_pos hs (mul_pos ha hb)
  linarith

/-- **The wall.**  For every coupling `β > 0` and every target `ρ < 1` there is
an extension `L` whose fused bond already beats `ρ`.  Hence `tanh (β · L)` is not
bounded away from `1`, and no `L`-uniform ratio bound survives the weight. -/
theorem exists_extension_exceeding {β : ℝ} (hβ : 0 < β) {ρ : ℝ} (hρ : ρ < 1) :
    ∃ L : ℕ, ρ < Real.tanh (β * L) := by
  -- Pick `L` with `β L` past `1 / (1 - ρ)`.  Then `e^{βL} ≥ βL + 1` already
  -- forces `e^{-βL} < 1 - ρ`, and `one_sub_tanh_le` turns that into the claim.
  -- No case split on the sign of `ρ` is needed: the bound is uniform.
  obtain ⟨L, hL⟩ := exists_nat_gt (1 / (1 - ρ) / β)
  refine ⟨L, ?_⟩
  have hr : (0 : ℝ) < 1 - ρ := by linarith
  have hbL : 1 / (1 - ρ) < β * L := by
    rw [div_lt_iff₀ hβ] at hL
    linarith [hL]
  have hEpos : 0 < Real.exp (β * L) := Real.exp_pos _
  have hE : 1 / (1 - ρ) < Real.exp (β * L) :=
    lt_of_lt_of_le hbL (by linarith [Real.add_one_le_exp (β * L)])
  have hneg : Real.exp (-(β * L)) < 1 - ρ := by
    rw [Real.exp_neg, inv_lt_iff_one_lt_mul₀ hEpos]
    -- clear the division in `hE` by `1 - ρ`, not by the exponential
    rw [div_lt_iff₀ hr] at hE
    linarith [hE, mul_comm (Real.exp (β * L)) (1 - ρ)]
  have hkey := one_sub_tanh_le (β * L)
  linarith

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
    have hcast : (1 : ℝ) < L := by exact_mod_cast hL
    nlinarith
  exact tanh_lt_tanh_of_lt h

/-- Both eigenvalues of a fused bond are nonzero, so its ratio is a genuine
ratio and the fragile half is not about a degenerate object. -/
theorem fused_nondegenerate {a : ℝ} (ha : 0 < a) :
    0 < 2 * Real.sinh a ∧ 0 < 2 * Real.cosh a := by
  refine ⟨?_, bond_top_pos a⟩
  have := Real.sinh_pos_iff.mpr ha
  linarith

/-! ## §6  Why the extremal congruence is a PAIR

Concentrating the weight uniformly on `m` sites of mutual correlation `μ` leaves
the exchangeable matrix `μ J + (1 - μ) I`.  Its spectrum is exactly two points —
`1 + (m-1)μ` on the constant vector, `1 - μ` on everything summing to zero — so
the ratio it reaches is `(1-μ) / (1 + (m-1)μ)`.

That ratio is **strictly decreasing in `m`**: the more sites the weight keeps,
the *smaller* the ratio it can reach.  Among uniform concentrations the best is
therefore the smallest nondegenerate one, a **pair** — which is exactly the
antipodal pair of §3 when the kernel is the hypercube one.

This is the provable core of an extremality that is otherwise only conjectural:
it settles the uniform-concentration family, and it says why the answer is a
pair rather than a larger cluster. It does **not** settle arbitrary weights. -/

/-- The exchangeable correlation matrix on `m` sites: `1` on the diagonal, `μ`
off it. -/
noncomputable def exch (m : ℕ) (μ : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i = j then 1 else μ

/-- **Top eigenvector.**  The constant vector, with eigenvalue `1 + (m-1)μ`. -/
theorem exch_mulVec_const (m : ℕ) (μ : ℝ) :
    (exch m μ).mulVec (fun _ => (1 : ℝ)) = fun _ => 1 + ((m : ℝ) - 1) * μ := by
  funext i
  simp only [exch, Matrix.mulVec, dotProduct, mul_one]
  have hsplit : ∀ j : Fin m,
      (if i = j then (1 : ℝ) else μ) = μ + (if i = j then 1 - μ else 0) := by
    intro j; by_cases h : i = j <;> simp [h]
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_ite_eq]
  simp
  ring

/-- **The rest of the spectrum.**  Everything summing to zero is an eigenvector
with eigenvalue `1 - μ`, so the spectrum really is only two points. -/
theorem exch_mulVec_of_sum_zero {m : ℕ} (μ : ℝ) {x : Fin m → ℝ}
    (hx : ∑ i, x i = 0) :
    (exch m μ).mulVec x = fun i => (1 - μ) * x i := by
  funext i
  simp only [exch, Matrix.mulVec, dotProduct]
  have hsplit : ∀ j : Fin m, (if i = j then (1 : ℝ) else μ) * x j
      = μ * x j + (if i = j then (1 - μ) * x i else 0) := by
    intro j
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h]
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib,
    ← Finset.mul_sum, hx, Finset.sum_ite_eq]
  simp

/-- **Pairs beat clusters.**  `(1-μ)/(1 + kμ)` is strictly decreasing in `k`, so
the exchangeable ratio falls as the concentration keeps more sites.  With
`k = m - 1` this says the best uniform concentration is the smallest one. -/
theorem exch_ratio_strict_anti {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    {k k' : ℝ} (hk : 0 ≤ k) (hlt : k < k') :
    (1 - μ) / (1 + k' * μ) < (1 - μ) / (1 + k * μ) := by
  have h1 : 0 < 1 + k * μ := by nlinarith
  have hnum : 0 < 1 - μ := by linarith
  have hden : 1 + k * μ < 1 + k' * μ := by nlinarith
  -- `a / b < a / c` for `0 < a` and `0 < c < b`; no identity to normalise
  exact div_lt_div_of_pos_left hnum h1 hden

/-- The pair value is the one §3 already computed: at `m = 2` the exchangeable
ratio is `(1-μ)/(1+μ)`, and on the hypercube kernel `μ = e^{-2βL}` at the
antipodal pair turns that into `tanh (βL)`. -/
theorem exch_ratio_pair (μ : ℝ) :
    (1 - μ) / (1 + ((2 : ℝ) - 1) * μ) = (1 - μ) / (1 + μ) := by
  norm_num

/-! ### §6.1  The supremum IS attained at `n = 2`

Recorded because an earlier draft of the companion paper asserted the opposite.
The two-point kernel `!![1, μ; μ, 1]` is its own least-correlated pair, and at
`D = I` — no concentration, no limit — its eigenvalues are already `1 + μ` and
`1 - μ`.  So the value `(1-μ)/(1+μ)` is reached, not merely approached, and any
claim of non-attainment is false as stated.

The claim was also incompatible with `crossRatio_congr_invariant`: that lemma
says the projective diameter is *constant* on the orbit, so nothing about it is
"attained only in the limit". -/

/-- The two-point unit-diagonal kernel, `exch 2 μ` written out. -/
theorem exch_two_apply (μ : ℝ) :
    exch 2 μ = !![1, μ; μ, 1] := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [exch]

/-- **Attainment at `n = 2`.**  The symmetric vector is an eigenvector with
eigenvalue `1 + μ`, the antisymmetric one with eigenvalue `1 - μ`; the ratio
`(1-μ)/(1+μ)` is therefore realised at `D = I`, with no limit taken. -/
theorem exch_two_eigen (μ : ℝ) :
    (exch 2 μ).mulVec ![1, 1] = (1 + μ) • ![1, 1] ∧
    (exch 2 μ).mulVec ![1, -1] = (1 - μ) • ![1, -1] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [exch_two_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-! ## §7  Strictly positive weights only: the orbit, not its closure

The fusion of §3 is realised by a weight that *concentrates*, and a reader is
entitled to ask whether that concentration leaves the object under study.  The
congruences here are by **strictly positive invertible** diagonals, whereas
"restricting to two configurations" sounds like setting the other diagonal
entries to zero — which lies in the *closure* of the orbit and not in the orbit.

It does not leave the orbit, and the reason is sharper than a limit argument.
Let `Dε` be `1` on two chosen configurations and `ε > 0` elsewhere.  Then for
**every** `ε > 0`, however small:

* `Dε` is strictly positive, so the congruence stays inside the orbit
  (`concentrate_pos`);
* the `2 × 2` block on the two chosen configurations is **exactly** the
  corresponding block of the original kernel, with no `ε` in it at all
  (`concentrate_block`);
* every entry touching any other configuration is at most `ε` times the
  corresponding entry of the kernel (`concentrate_off_block`).

So **the fused bond is already present at every strictly positive `ε`**; what
the limit does is delete the rest of the matrix, not create the block.  Turning
that deletion into a statement about eigenvalues is the classical continuity of
the spectrum in finite dimensions, which is cited in the paper and not reproved
here — the interface is this section, and it is stated rather than assumed. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The concentrating weight: `1` at `p` and `q`, `ε` everywhere else. -/
def concentrate (p q : n) (ε : ℝ) : n → ℝ :=
  fun i => if i = p then 1 else if i = q then 1 else ε

omit [Fintype n] in
/-- It really is a strictly positive weight, so the congruence never leaves the
orbit of invertible positive diagonals. -/
theorem concentrate_pos {ε : ℝ} (hε : 0 < ε) (p q i : n) :
    0 < concentrate p q ε i := by
  unfold concentrate
  split
  · norm_num
  · split
    · norm_num
    · exact hε

omit [Fintype n] in
/-- `ε ≤ 1` makes every weight at most one — the only bound §7.3 needs. -/
theorem concentrate_le_one {ε : ℝ} (hε : ε ≤ 1) (p q i : n) :
    concentrate p q ε i ≤ 1 := by
  unfold concentrate
  split
  · exact le_refl 1
  · split
    · exact le_refl 1
    · exact hε

/-- **The block is exact.**  On the two chosen configurations the congruence
leaves the kernel completely alone, for every `ε` — including the diagonal
entries, since `p ≠ q` is not even needed. -/
theorem concentrate_block (M : Matrix n n ℝ) (p q : n) (ε : ℝ) :
    (Matrix.diagonal (concentrate p q ε) * M * Matrix.diagonal (concentrate p q ε)) p q
      = M p q := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold concentrate
  simp

/-- The mirrored entry, likewise untouched. -/
theorem concentrate_block' (M : Matrix n n ℝ) (p q : n) (ε : ℝ) :
    (Matrix.diagonal (concentrate p q ε) * M * Matrix.diagonal (concentrate p q ε)) q p
      = M q p := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold concentrate
  by_cases h : q = p
  · simp [h]
  · simp [h]

/-- **Everything else is `O(ε)`.**  Any entry whose row leaves the pair is
damped by at least a factor `ε`. -/
theorem concentrate_off_block {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (M : Matrix n n ℝ) (p q i j : n) (hip : i ≠ p) (hiq : i ≠ q) :
    |(Matrix.diagonal (concentrate p q ε) * M *
        Matrix.diagonal (concentrate p q ε)) i j| ≤ ε * |M i j| := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hi : concentrate p q ε i = ε := by
    unfold concentrate; rw [if_neg hip, if_neg hiq]
  rw [hi, abs_mul, abs_mul, abs_of_pos hε0]
  have hj0 : 0 < concentrate p q ε j := concentrate_pos hε0 p q j
  have hj1 : |concentrate p q ε j| ≤ 1 := by
    rw [abs_of_pos hj0]; exact concentrate_le_one hε1 p q j
  calc ε * |M i j| * |concentrate p q ε j| ≤ ε * |M i j| * 1 :=
        mul_le_mul_of_nonneg_left hj1 (by positivity)
    _ = ε * |M i j| := by ring

/-- **The fused bond, at every `ε`.**  Specialised to the antipodal pair of the
hypercube kernel, the block the concentration preserves is exactly the Ising
bond of coupling `β · L` — for every strictly positive `ε`, not only in a limit.
This is §3's fusion identity relocated inside the orbit. -/
theorem concentrate_antipodal_block (L : ℕ) (β ε : ℝ) :
    (Matrix.diagonal (concentrate (cfgPlus L) (cfgMinus L) ε) *
       Matrix.of (fun σ τ => tensorKernel L β σ τ) *
       Matrix.diagonal (concentrate (cfgPlus L) (cfgMinus L) ε))
        (cfgPlus L) (cfgMinus L)
      = Real.exp (-(β * L)) := by
  rw [concentrate_block]
  exact tensorKernel_plus_minus L β

/-! ## §8  The upper bound, via Hilbert's projective diameter

This section supplies what §5 of the paper could previously only conjecture.

For an entrywise positive matrix `T`, Hilbert's projective diameter is
`Δ(T) = max log (T i k * T j l / (T j k * T i l))`, and Birkhoff's theorem says
the induced map contracts the Hilbert metric by `tanh (Δ/4)`; the spectral
consequence — `|λ₁| / λ₀ ≤ tanh (Δ/4)` — is classical (Birkhoff 1957;
Eveson–Nussbaum 1995).  **That classical input is cited by the paper and is not
reproved here.**  What is proved here are the two facts that make it bite, and
both are elementary:

* **§8.1 the diameter is a congruence invariant** — the weights cancel out of
  the cross-ratio identically, so `Δ(D M D) = Δ(M)` for every positive `D`;
* **§8.2 the diameter of a unit-diagonal `M` with entries in `[μ,1]` is exactly
  `2 log (1/μ)`** — the maximum is attained at `i = k`, `j = l` on the least
  correlated pair;

and **§8.3** the scalar identity `tanh ((1/2) log (1/μ)) = (1-μ)/(1+μ)`.

Chaining them: `sup_D r(D M D) ≤ tanh (Δ(M)/4) = (1-μ)/(1+μ)`, and §6 already
gives the matching lower bound.  Note what the argument never uses: **any
definiteness assumption**.  Only positivity of the entries.  That is exactly why
the twelve indefinite witnesses of the lane's judge JB all obeyed the bound —
the failed prediction was pointing at this section. -/

/-! ### §8.1  The weights cancel -/

/-- Congruence multiplies the numerator of the cross-ratio by `d i d j d k d l`. -/
theorem crossProd_congr (M : Matrix n n ℝ) (d : n → ℝ) (i j k l : n) :
    (Matrix.diagonal d * M * Matrix.diagonal d) i k *
      (Matrix.diagonal d * M * Matrix.diagonal d) j l
      = (d i * d j * d k * d l) * (M i k * M j l) := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  ring

/-- **The diameter is a congruence invariant.**  The denominator of the
cross-ratio picks up the *same* factor `d i d j d k d l` as the numerator, so the
ratio — and hence Hilbert's projective diameter — does not move at all.  This is
the whole mechanism of §8: a positive weight cannot change the projective
geometry it acts on. -/
theorem crossRatio_congr_invariant (M : Matrix n n ℝ) (d : n → ℝ) (i j k l : n) :
    (Matrix.diagonal d * M * Matrix.diagonal d) i k *
      (Matrix.diagonal d * M * Matrix.diagonal d) j l *
      (M j k * M i l)
    = (M i k * M j l) *
      ((Matrix.diagonal d * M * Matrix.diagonal d) j k *
        (Matrix.diagonal d * M * Matrix.diagonal d) i l) := by
  rw [crossProd_congr, crossProd_congr]
  ring

/-! ### §8.2  The diameter of a unit-diagonal kernel -/

omit [Fintype n] [DecidableEq n] in
/-- **Every cross-ratio is at most `1/μ²`.**  Stated multiplicatively, so no
division and no logarithm appear: `μ² · (numerator) ≤ (denominator)`. -/
theorem crossRatio_le_of_bounds {M : Matrix n n ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hlo : ∀ a b, μ ≤ M a b) (hhi : ∀ a b, M a b ≤ 1) (i j k l : n) :
    μ * μ * (M i k * M j l) ≤ M j k * M i l := by
  have h1 : M i k * M j l ≤ 1 :=
    mul_le_one₀ (hhi i k) (le_trans hμ.le (hlo j l)) (hhi j l)
  have h2 : μ * μ ≤ M j k * M i l :=
    mul_le_mul (hlo j k) (hlo i l) hμ.le (le_trans hμ.le (hlo j k))
  nlinarith [hμ, h1, h2, hlo j k, hlo i l]

omit [Fintype n] [DecidableEq n] in
/-- **And `1/μ²` is attained.**  Taking `i = k` and `j = l` on a pair realising
the minimum turns the cross-ratio into `1 / (M i j)² = 1/μ²`, so the bound of
`crossRatio_le_of_bounds` is exactly the diameter and not merely an estimate. -/
theorem crossRatio_attained {M : Matrix n n ℝ} {μ : ℝ} (i j : n)
    (hii : M i i = 1) (hjj : M j j = 1) (hij : M i j = μ) (hji : M j i = μ) :
    M i i * M j j = 1 ∧ M j i * M i j = μ * μ := by
  refine ⟨by rw [hii, hjj]; ring, by rw [hji, hij]⟩

/-! ### §8.3  From the diameter to the ratio -/

/-- **The identity that converts `Δ` into the bound.**  With `t = e^{Δ/4}`, so
that `t² = 1/μ`, the Birkhoff contraction coefficient `tanh (Δ/4)` equals
`(1-μ)/(1+μ)`.  Written without `log` so that nothing depends on the branch. -/
theorem ratio_of_sq {t μ : ℝ} (ht : 0 < t) (hμ : 0 < μ) (hsq : t * t = 1 / μ) :
    (t - t⁻¹) / (t + t⁻¹) = (1 - μ) / (1 + μ) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hden : 0 < t + t⁻¹ := by positivity
  -- clear the inverses first: multiplying numerator and denominator by `t`
  -- turns the quotient into `(t² - 1)/(t² + 1)`
  have key : (t - t⁻¹) / (t + t⁻¹) = (t * t - 1) / (t * t + 1) := by
    rw [div_eq_div_iff (ne_of_gt hden) (by positivity)]
    field_simp
  rw [key, hsq]
  -- and `t² = 1/μ` makes it `(1/μ - 1)/(1/μ + 1) = (1-μ)/(1+μ)`, a field identity
  rw [div_eq_div_iff (by positivity) (by linarith)]
  field_simp

/-- `tanh` at a quarter-diameter, in the exponential form `ratio_of_sq` needs. -/
theorem tanh_eq_exp_ratio (x : ℝ) :
    Real.tanh x = (Real.exp x - (Real.exp x)⁻¹) / (Real.exp x + (Real.exp x)⁻¹) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, ← Real.exp_neg]
  have h : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
  rw [Real.exp_neg]
  field_simp

/-- **The bound in closed form.**  `tanh ((1/2) log (1/μ)) = (1-μ)/(1+μ)`.  With
`Δ = 2 log (1/μ)` from §8.2 this is exactly `tanh (Δ/4)`, so the Birkhoff
contraction coefficient of the congruence class is `(1-μ)/(1+μ)` — the value §6
attains from below. -/
theorem tanh_half_log_inv {μ : ℝ} (hμ0 : 0 < μ) :
    Real.tanh (Real.log (1 / μ) / 2) = (1 - μ) / (1 + μ) := by
  have hinv : (0 : ℝ) < 1 / μ := by positivity
  set x := Real.log (1 / μ) / 2 with hx
  have hsq : Real.exp x * Real.exp x = 1 / μ := by
    rw [← Real.exp_add, hx, show Real.log (1 / μ) / 2 + Real.log (1 / μ) / 2
      = Real.log (1 / μ) from by ring]
    exact Real.exp_log hinv
  rw [tanh_eq_exp_ratio]
  exact ratio_of_sq (Real.exp_pos x) hμ0 hsq

/-! ## §9  Killing the continuity import in the lower bound

The lower bound of the supremum theorem was proved on paper by letting
`T_ε = D_ε M D_ε` converge entrywise to the two-point block plus zeros and citing
finite-dimensional continuity of eigenvalues.  That citation is avoidable.

Let `Ω > 0` be the Perron vector of `T_ε` and put

    x = Ω q • e_p  -  Ω p • e_q .

Then `⟪Ω, x⟫ = 0` for free, `x` is supported on `{p,q}` so the rest of the matrix
never enters its quadratic form, and --- this is the point --- the Rayleigh
quotient of `x` is bounded below by `1 - μ` **as a ring identity plus one
square**:

    a² + b² - 2μ a b  =  (1-μ)(a² + b²)  +  μ (a - b)² .

Combined with `ρ(T_ε) ≤ max row sum ≤ 1 + μ + nε`, this gives
`r(T_ε) ≥ (1-μ)/(1+μ+nε)`, and the supremum follows from a scalar `ε → 0`
argument.  No eigenvalue enumeration and no spectral continuity anywhere.

Verified numerically before being written (61/61 checks, `n ∈ {3,5,8}`,
`μ ∈ {0.2,0.55}`, `ε ∈ {10⁻¹,10⁻³}`): the Rayleigh quotient lands on `1 - μ` to
nine decimals, and the chain never fails.

What is proved here is the algebra of that route.  Assembling it into a
statement about `specRatio` still needs a Perron-vector interface, and is the
next brick rather than this one. -/

/-! ### §9.1  The Rayleigh identity, and why the slack is a square -/

/-- **The identity.**  Everything the witness needs is one line of `ring`. -/
theorem witness_quad_identity (a b μ : ℝ) :
    a * a + b * b - 2 * μ * (a * b)
      = (1 - μ) * (a * a + b * b) + μ * (a - b) ^ 2 := by
  ring

/-- **The Rayleigh bound.**  For `0 ≤ μ` the two-supported witness has quadratic
form at least `(1-μ)` times its squared norm.  The slack is `μ (a-b)²`, so the
bound is an equality exactly when `a = b`. -/
theorem witness_quad_lower {a b μ : ℝ} (hμ : 0 ≤ μ) :
    (1 - μ) * (a * a + b * b) ≤ a * a + b * b - 2 * μ * (a * b) := by
  rw [witness_quad_identity]
  nlinarith [sq_nonneg (a - b), hμ]

/-- The slack, named: the bound is sharp precisely on the diagonal `a = b`. -/
theorem witness_quad_eq_iff {a b μ : ℝ} (hμ : 0 < μ) :
    (1 - μ) * (a * a + b * b) = a * a + b * b - 2 * μ * (a * b) ↔ a = b := by
  rw [witness_quad_identity]
  constructor
  · intro h
    have hsq : (a - b) ^ 2 = 0 := by
      have : μ * (a - b) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h2
      · exact absurd h1 (ne_of_gt hμ)
      · exact h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linarith [this]
  · intro h; rw [h]; ring

/-! ### §9.2  The two-supported test vector -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `a` at `p`, `-b` at `q`, zero elsewhere. -/
def pairVec (p q : n) (a b : ℝ) : n → ℝ :=
  fun i => if i = p then a else if i = q then -b else 0

omit [Fintype n] in
theorem pairVec_at_p {p q : n} (a b : ℝ) : pairVec p q a b p = a := by
  simp [pairVec]

omit [Fintype n] in
theorem pairVec_at_q {p q : n} (hpq : p ≠ q) (a b : ℝ) :
    pairVec p q a b q = -b := by
  simp [pairVec, Ne.symm hpq]

omit [Fintype n] in
theorem pairVec_off {p q i : n} (hip : i ≠ p) (hiq : i ≠ q) (a b : ℝ) :
    pairVec p q a b i = 0 := by
  simp [pairVec, hip, hiq]

/-- **Orthogonality is free.**  Choosing `a = Ω q` and `b = Ω p` makes the
witness orthogonal to `Ω` with no hypothesis on `Ω` at all --- the two surviving
terms cancel identically. -/
theorem pairVec_orthogonal {p q : n} (hpq : p ≠ q) (Ω : n → ℝ) :
    ∑ i, Ω i * pairVec p q (Ω q) (Ω p) i = 0 := by
  have hsub : ∀ i ∈ (Finset.univ : Finset n), i ∉ ({p, q} : Finset n) →
      Ω i * pairVec p q (Ω q) (Ω p) i = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [pairVec_off hi.1 hi.2, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ ({p, q} : Finset n)) hsub,
    Finset.sum_pair hpq, pairVec_at_p, pairVec_at_q hpq]
  ring

/-! ### §9.3  The scalar limit that finishes the lower bound -/

/-- **The `ε → 0` step.**  `(1-μ)/(1+μ+c·ε)` exceeds every number strictly below
`(1-μ)/(1+μ)` once `ε` is small enough, so the supremum of the left-hand family
is the right-hand value.  Stated with an explicit witness rather than a limit. -/
theorem lower_bound_approaches {μ c : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : 0 < c)
    {t : ℝ} (ht : t < (1 - μ) / (1 + μ)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ t < (1 - μ) / (1 + μ + c * ε) := by
  have hden : (0 : ℝ) < 1 + μ := by linarith
  have hnum : (0 : ℝ) < 1 - μ := by linarith
  by_cases hpos : 0 < t
  · -- `t > 0`: solve `t (1 + μ + cε) < 1 - μ` for `ε`, explicitly
    have ht0 : t ≠ 0 := ne_of_gt hpos
    have hc0 : c ≠ 0 := ne_of_gt hc
    have hkey : t * (1 + μ) < 1 - μ := by
      rw [lt_div_iff₀ hden] at ht; linarith
    have h2tc : (0 : ℝ) < 2 * t * c := mul_pos (mul_pos (by norm_num) hpos) hc
    obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = (1 - μ - t * (1 + μ)) / (2 * t * c) := ⟨_, rfl⟩
    have hE : 0 < E := by rw [hEdef]; exact div_pos (by linarith) h2tc
    have hexp : t * (c * E) = (1 - μ - t * (1 + μ)) / 2 := by
      rw [hEdef]; field_simp; all_goals ring
    have hminpos : 0 < min E 1 := lt_min hE one_pos
    refine ⟨min E 1, hminpos, min_le_right _ _, ?_⟩
    have hd2 : (0 : ℝ) < 1 + μ + c * min E 1 := by
      have := mul_pos hc hminpos; linarith
    rw [lt_div_iff₀ hd2]
    have hstep : t * (c * min E 1) ≤ t * (c * E) := by
      have htc : (0 : ℝ) ≤ t * c := le_of_lt (mul_pos hpos hc)
      nlinarith [min_le_left E 1, htc]
    have hmul : t * (1 + μ + c * min E 1) = t * (1 + μ) + t * (c * min E 1) := by ring
    rw [hmul]
    linarith
  · exact ⟨1, one_pos, le_refl 1,
      lt_of_le_of_lt (not_lt.mp hpos) (div_pos hnum (by linarith))⟩

/-! ## §10  The conditional theorem: an exact least upper bound

The main theorem of the paper has two imported inputs — Birkhoff's contraction
bound for the upper half, and a Perron vector for the lower half — and a body of
glue that is entirely elementary.  §10 separates them.

Both imports enter as **explicit hypotheses of the theorem**, never as `axiom`
declarations: a reader who does not grant them gets a true implication and no
claim.  Everything between them is proved here: that the cross-ratio is a
congruence invariant (§8), that the fluctuation witness is orthogonal and has
the right Rayleigh quotient (§9), and that the resulting family of lower bounds
has the stated supremum (§9.3).

Two deliberate weakenings, both in the direction of assuming *less*:

* `hBirkhoff` is stated in Seneta's logarithm-free form — no `log`, no `tanh`,
  only `Real.sqrt` — and with `φ` merely *a* lower bound for the cross-ratios
  rather than their minimum.  Since `x ↦ (1-x)/(1+x)` is decreasing, this
  version is *implied* by the sharp one.
* `hConc` asks only for the lower bound at each positive `ε ≤ 1`, not for a
  limit.  No spectral continuity appears anywhere in §10; the `ε → 0` step is
  the scalar `lower_bound_approaches`, which produces an explicit witness. -/

/-- Everything a strictly positive diagonal congruence can reach. -/
def congrOrbit (r : Matrix n n ℝ → ℝ) (M : Matrix n n ℝ) : Set ℝ :=
  {x | ∃ d : n → ℝ, (∀ i, 0 < d i) ∧
        x = r (Matrix.diagonal d * M * Matrix.diagonal d)}

theorem mem_congrOrbit (r : Matrix n n ℝ → ℝ) (M : Matrix n n ℝ) {d : n → ℝ}
    (hd : ∀ i, 0 < d i) :
    r (Matrix.diagonal d * M * Matrix.diagonal d) ∈ congrOrbit r M :=
  ⟨d, hd, rfl⟩

/-- Non-vacuity, first half: the set the supremum is taken over is never empty,
so `IsLUB` below is not a statement about `∅`. -/
theorem congrOrbit_nonempty (r : Matrix n n ℝ → ℝ) (M : Matrix n n ℝ) :
    (congrOrbit r M).Nonempty :=
  ⟨_, mem_congrOrbit r M (d := fun _ => (1 : ℝ)) (fun _ => one_pos)⟩

/-! ### §10.1  The upper half, from Birkhoff -/

/-- **The upper bound.**  Granted Birkhoff's bound as a hypothesis, the whole
congruence orbit lies below `(1-μ)/(1+μ)`.  The proof is §8 and nothing else:
the congruence multiplies numerator and denominator of every cross-ratio by the
same factor, so the bound available at `M` is available at every `DMD`. -/
theorem congrOrbit_upper_of_birkhoff
    {r : Matrix n n ℝ → ℝ} {M : Matrix n n ℝ} {μ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hlo : ∀ a b, μ ≤ M a b) (hhi : ∀ a b, M a b ≤ 1)
    (hBirkhoff : ∀ (T : Matrix n n ℝ) (φ : ℝ), 0 < φ → φ ≤ 1 →
        (∀ i j k l, φ * (T j k * T i l) ≤ T i k * T j l) →
        r T ≤ (1 - Real.sqrt φ) / (1 + Real.sqrt φ)) :
    ∀ x ∈ congrOrbit r M, x ≤ (1 - μ) / (1 + μ) := by
  rintro x ⟨d, hd, rfl⟩
  have hcross : ∀ i j k l,
      (μ * μ) * ((Matrix.diagonal d * M * Matrix.diagonal d) j k *
          (Matrix.diagonal d * M * Matrix.diagonal d) i l)
        ≤ (Matrix.diagonal d * M * Matrix.diagonal d) i k *
          (Matrix.diagonal d * M * Matrix.diagonal d) j l := by
    intro i j k l
    have hw : (0 : ℝ) ≤ d i * d j * d k * d l :=
      le_of_lt (mul_pos (mul_pos (mul_pos (hd i) (hd j)) (hd k)) (hd l))
    have hM := crossRatio_le_of_bounds hμ0 hlo hhi j i k l
    have key := mul_le_mul_of_nonneg_left hM hw
    rw [crossProd_congr M d i j k l, crossProd_congr M d j i k l]
    nlinarith [key]
  have hφ0 : (0 : ℝ) < μ * μ := mul_pos hμ0 hμ0
  have hφ1 : μ * μ ≤ 1 := by nlinarith
  have hres := hBirkhoff _ (μ * μ) hφ0 hφ1 hcross
  rwa [Real.sqrt_mul_self hμ0.le] at hres

/-! ### §10.2  The lower half, without spectral continuity -/

/-- A sum whose summand vanishes off a pair collapses to two terms. -/
theorem sum_eq_pair_of_vanishing {p q : n} (hpq : p ≠ q) (g : n → ℝ)
    (hg : ∀ i, i ≠ p → i ≠ q → g i = 0) : ∑ i, g i = g p + g q := by
  have hsub : ∀ i ∈ (Finset.univ : Finset n), i ∉ ({p, q} : Finset n) → g i = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact hg i hi.1 hi.2
  rw [← Finset.sum_subset (Finset.subset_univ ({p, q} : Finset n)) hsub,
    Finset.sum_pair hpq]

/-- The quadratic form of a two-supported vector sees only the `2×2` block.
This is what makes the lower bound elementary: the rest of the matrix, however
large, contributes nothing to the witness. -/
theorem quad_pairVec (M : Matrix n n ℝ) {p q : n} (hpq : p ≠ q) (a b : ℝ) :
    quad M (pairVec p q a b)
      = a * M p p * a + a * M p q * (-b) + ((-b) * M q p * a + (-b) * M q q * (-b)) := by
  have hinner : ∀ i : n, ∑ j, pairVec p q a b i * M i j * pairVec p q a b j
      = pairVec p q a b i * M i p * a + pairVec p q a b i * M i q * (-b) := by
    intro i
    have h := sum_eq_pair_of_vanishing hpq
      (fun j => pairVec p q a b i * M i j * pairVec p q a b j)
      (fun j hjp hjq => by rw [pairVec_off hjp hjq]; ring)
    rw [h]
    simp only [pairVec_at_p, pairVec_at_q hpq]
  unfold quad
  rw [sum_eq_pair_of_vanishing hpq
    (fun i => ∑ j, pairVec p q a b i * M i j * pairVec p q a b j)
    (fun i hip hiq => by
      simp only [pairVec_off hip hiq, zero_mul, Finset.sum_const_zero])]
  simp only [hinner, pairVec_at_p, pairVec_at_q hpq]
  all_goals ring

/-- **The fluctuation witness at the least-correlated pair.**  Both halves of
what the lower bound needs, with no eigenvalue and no limit: the witness is
orthogonal to *any* candidate Perron vector `Ω`, and its Rayleigh quotient is at
least `1 - μ`.  The slack is `μ (Ω p - Ω q)²`, which is why the bound is exactly
`1 - μ` and not less. -/
theorem leastPair_fluctuation_witness
    {M : Matrix n n ℝ} {μ : ℝ} {p q : n} (hpq : p ≠ q) (hμ : 0 ≤ μ)
    (hpp : M p p = 1) (hqq : M q q = 1) (hpqv : M p q = μ) (hqpv : M q p = μ)
    (Ω : n → ℝ) :
    (∑ i, Ω i * pairVec p q (Ω q) (Ω p) i = 0) ∧
      (1 - μ) * (∑ i, pairVec p q (Ω q) (Ω p) i * pairVec p q (Ω q) (Ω p) i)
        ≤ quad M (pairVec p q (Ω q) (Ω p)) := by
  refine ⟨pairVec_orthogonal hpq Ω, ?_⟩
  have hnorm : ∑ i, pairVec p q (Ω q) (Ω p) i * pairVec p q (Ω q) (Ω p) i
      = Ω q * Ω q + Ω p * Ω p := by
    rw [sum_eq_pair_of_vanishing hpq
      (fun i => pairVec p q (Ω q) (Ω p) i * pairVec p q (Ω q) (Ω p) i)
      (fun i hip hiq => by rw [pairVec_off hip hiq]; ring)]
    simp only [pairVec_at_p, pairVec_at_q hpq]
    ring
  rw [hnorm, quad_pairVec M hpq, hpp, hqq, hpqv, hqpv]
  nlinarith [witness_quad_lower (a := Ω q) (b := Ω p) hμ]

/-- The division step, isolated.  A Perron root no larger than a row-sum bound
and a fluctuation no smaller than `1 - μ` give a ratio bound — and this is the
*only* place the Perron root is used at all. -/
theorem leastPair_specGap_lower {μ ε c ρ s : ℝ} (hμ1 : μ < 1)
    (hρ0 : 0 < ρ) (hρa : ρ ≤ 1 + μ + c * ε) (hs : 1 - μ ≤ s) :
    (1 - μ) / (1 + μ + c * ε) ≤ s / ρ := by
  have ha : (0 : ℝ) < 1 + μ + c * ε := lt_of_lt_of_le hρ0 hρa
  have hb : (0 : ℝ) ≤ 1 - μ := by linarith
  have hexp : s / ρ - (1 - μ) / (1 + μ + c * ε)
      = (s * (1 + μ + c * ε) - (1 - μ) * ρ) / (ρ * (1 + μ + c * ε)) := by
    field_simp
    all_goals ring
  have hnn : 0 ≤ (s * (1 + μ + c * ε) - (1 - μ) * ρ) / (ρ * (1 + μ + c * ε)) :=
    div_nonneg (by nlinarith) (le_of_lt (mul_pos hρ0 ha))
  have : 0 ≤ s / ρ - (1 - μ) / (1 + μ + c * ε) := by rw [hexp]; exact hnn
  linarith

/-- **Every value below `(1-μ)/(1+μ)` is beaten inside the orbit.**  Not in its
closure, and not in a limit: for each such `t` an explicit `ε` is produced, and
the concentrating weight at that `ε` is strictly positive. -/
theorem concentrated_specRatio_approaches
    {r : Matrix n n ℝ → ℝ} {M : Matrix n n ℝ} {μ c : ℝ} {p q : n}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : 0 < c)
    (hConc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (1 - μ) / (1 + μ + c * ε) ≤
          r (Matrix.diagonal (concentrate p q ε) * M *
            Matrix.diagonal (concentrate p q ε)))
    {t : ℝ} (ht : t < (1 - μ) / (1 + μ)) :
    ∃ x ∈ congrOrbit r M, t < x := by
  obtain ⟨ε, hε0, hε1, hlt⟩ := lower_bound_approaches hμ0 hμ1 hc ht
  exact ⟨_, mem_congrOrbit r M (fun i => concentrate_pos hε0 p q i),
    lt_of_lt_of_le hlt (hConc ε hε0 hε1)⟩

/-! ### §10.3  The two halves compose -/

/-- **The conditional main theorem.**  Granted Birkhoff's bound (`hBirkhoff`) and
the concentrated lower bound (`hConc`), `(1-μ)/(1+μ)` is the *least* upper bound
of the congruence orbit — an equality, not an estimate.

Neither hypothesis is an axiom of this development, and neither is proved here.
What is proved is that nothing else is needed: the reduction of Birkhoff's bound
at `DMD` to its value at `M`, the elimination of the limit, and the composition
into `IsLUB` are all mechanical. -/
theorem congruenceRatio_isLUB_of_birkhoff
    {r : Matrix n n ℝ → ℝ} {M : Matrix n n ℝ} {μ c : ℝ} {p q : n}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : 0 < c)
    (hlo : ∀ a b, μ ≤ M a b) (hhi : ∀ a b, M a b ≤ 1)
    (hBirkhoff : ∀ (T : Matrix n n ℝ) (φ : ℝ), 0 < φ → φ ≤ 1 →
        (∀ i j k l, φ * (T j k * T i l) ≤ T i k * T j l) →
        r T ≤ (1 - Real.sqrt φ) / (1 + Real.sqrt φ))
    (hConc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (1 - μ) / (1 + μ + c * ε) ≤
          r (Matrix.diagonal (concentrate p q ε) * M *
            Matrix.diagonal (concentrate p q ε))) :
    IsLUB (congrOrbit r M) ((1 - μ) / (1 + μ)) := by
  constructor
  · intro x hx
    exact congrOrbit_upper_of_birkhoff hμ0 hμ1.le hlo hhi hBirkhoff x hx
  · intro y hy
    by_contra hcon
    push_neg at hcon
    obtain ⟨x, hxmem, hxgt⟩ :=
      concentrated_specRatio_approaches (p := p) (q := q) hμ0 hμ1 hc hConc hcon
    exact absurd (hy hxmem) (not_le.mpr hxgt)

/-- Non-vacuity, second half: the value the theorem pins is strictly positive
whenever `μ < 1`, so the conclusion is not the trivial `IsLUB … 0`.  Together
with `congrOrbit_nonempty` and the `n = 2` attainment of `exch_two_eigen`, the
statement has content at every admissible `μ`. -/
theorem isLUB_value_pos {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    0 < (1 - μ) / (1 + μ) :=
  div_pos (by linarith) (by linarith)

end Congruence

end YangMills.OS
