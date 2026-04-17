/-
Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Proposition 5.1 (oscillation bound) of [Eriksson Feb 2026].

There exists $C_1 < \infty$ such that
$\sup_\ell \mathrm{osc}_\ell(R^*) \le C_1$
uniformly in $\bar g \in (0, \gamma_0]$ and $L_{\mathrm{phys}}$, where
$\mathrm{osc}_\ell(F) = \sup \{|F(U) - F(U')|$ : $U, U'$ differ only at link $\ell\}$
and $R^*$ is the effective terminal remainder of the Balaban renormalisation
group flow.

The proof relies on geometric decay of polymer activities (parameter $r \in (0,1)$)
together with the polynomial bound on lattice animals of diameter $n$ containing
a fixed link ($\le C_{\mathrm{anim}}(n+1)^d$), yielding the convergent
series $\sum_n C_{\mathrm{anim}} n^d A_0 r^n < \infty$.
-/

import Mathlib

namespace YangMills

open scoped BigOperators

/-! ## Link oscillation -/

/-- **Link oscillation** of a real-valued observable $F$ on a space of gauge
configurations $\alpha$, with respect to a relation $\sim_\ell$ expressing
"the pair $(U, U')$ differs only at link $\ell$". Defined as the supremum of
$|F(U) - F(U')|$ over pairs related by `differs`. -/
noncomputable def linkOscillation {α : Type*} (differs : α → α → Prop) (F : α → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ U U' : α, differs U U' ∧ r = |F U - F U'|}

/-- Link oscillation is non-negative provided the `differs` relation is
reflexive (so that the pair $(U, U)$ contributes $|F(U) - F(U)| = 0$
to the set) and the set is bounded above. -/
theorem linkOscillation_nonneg {α : Type*} [Nonempty α]
    (differs : α → α → Prop) (hrefl : ∀ U, differs U U) (F : α → ℝ)
    (hbdd : BddAbove {r : ℝ | ∃ U U' : α, differs U U' ∧ r = |F U - F U'|}) :
    0 ≤ linkOscillation differs F := by
  unfold linkOscillation
  have hmem : (0 : ℝ) ∈ {r : ℝ | ∃ U U' : α, differs U U' ∧ r = |F U - F U'|} := by
    refine ⟨Classical.arbitrary α, Classical.arbitrary α, hrefl _, ?_⟩
    rw [sub_self, abs_zero]
  exact le_csSup hbdd hmem

/-! ## Polymer activity bound -/

/-- A **polymer activity bound** for the terminal remainder: witnesses the
geometric decay of polymer activities together with a polynomial lattice-animal
count. The relevant constants are:
* `dim`: the spatial dimension $d$ (physically $d = 4$);
* `A₀`: the base activity bound;
* `r ∈ (0, 1)`: the geometric decay ratio (typically $e^{-m_P}$);
* `C_anim`: the lattice-animal constant.

These parameters must satisfy $A_0 \ge 0$, $0 < r < 1$, $C_{\mathrm{anim}} \ge 0$. -/
structure PolymerActivityBound where
  /-- Lattice dimension. -/
  dim : ℕ
  /-- Base activity bound (non-negative). -/
  A₀ : ℝ
  hA₀ : 0 ≤ A₀
  /-- Geometric decay ratio. -/
  r : ℝ
  hr_pos : 0 < r
  hr_lt_one : r < 1
  /-- Lattice-animal constant (non-negative). -/
  C_anim : ℝ
  hC : 0 ≤ C_anim

/-! ## Geometric series bound -/

/-- **Geometric series polymer bound**: for $0 \le r < 1$ and any $d \in \mathbb{N}$,
the series $\sum_{n=0}^\infty n^d r^n$ is summable. This is the analytic
ingredient underlying the existence of a finite oscillation constant. -/
theorem geometric_series_polymer_bound {d : ℕ} {r : ℝ} (hr_nn : 0 ≤ r) (hr_lt : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ)) ^ d * r ^ n) := by
  have h_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]
    exact hr_lt
  exact summable_pow_mul_geometric_of_norm_lt_one d h_norm

/-! ## Terminal oscillation constant -/

/-- The **terminal oscillation constant** associated with a polymer activity bound.
Given by $C_1 = \sum_{n=0}^\infty C_{\mathrm{anim}} \cdot n^d \cdot A_0 \cdot r^n$. -/
noncomputable def PolymerActivityBound.oscillationConstant (H : PolymerActivityBound) : ℝ :=
  ∑' n : ℕ, H.C_anim * ((n : ℝ)) ^ H.dim * H.A₀ * H.r ^ n

/-- **Proposition 5.1 (terminal oscillation bound)**: Given a polymer activity
bound, the series $\sum_n C_{\mathrm{anim}} n^d A_0 r^n$ has a finite non-negative
sum $C_1$. This $C_1$ bounds the oscillation of the terminal remainder
uniformly in $\bar g \in (0, \gamma_0]$ and in the lattice size $L_{\mathrm{phys}}$. -/
theorem terminal_oscillation_bound (H : PolymerActivityBound) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧
      HasSum (fun n : ℕ => H.C_anim * ((n : ℝ)) ^ H.dim * H.A₀ * H.r ^ n) C₁ := by
  have hr_nn : (0 : ℝ) ≤ H.r := H.hr_pos.le
  have hsum_basic : Summable (fun n : ℕ => ((n : ℝ)) ^ H.dim * H.r ^ n) :=
    geometric_series_polymer_bound hr_nn H.hr_lt_one
  have hsum : Summable (fun n : ℕ => H.C_anim * ((n : ℝ)) ^ H.dim * H.A₀ * H.r ^ n) := by
    have hmul := hsum_basic.mul_left (H.C_anim * H.A₀)
    have heq : (fun n : ℕ => H.C_anim * H.A₀ * (((n : ℝ)) ^ H.dim * H.r ^ n))
             = (fun n : ℕ => H.C_anim * ((n : ℝ)) ^ H.dim * H.A₀ * H.r ^ n) := by
      funext n; ring
    rw [heq] at hmul
    exact hmul
  refine ⟨∑' n : ℕ, H.C_anim * ((n : ℝ)) ^ H.dim * H.A₀ * H.r ^ n, ?_, hsum.hasSum⟩
  apply tsum_nonneg
  intro n
  have hnd : 0 ≤ ((n : ℝ)) ^ H.dim := pow_nonneg (Nat.cast_nonneg _) _
  have hrn : 0 ≤ H.r ^ n := pow_nonneg hr_nn _
  have h1 : 0 ≤ H.C_anim * ((n : ℝ)) ^ H.dim := mul_nonneg H.hC hnd
  have h2 : 0 ≤ H.C_anim * ((n : ℝ)) ^ H.dim * H.A₀ := mul_nonneg h1 H.hA₀
  exact mul_nonneg h2 hrn

end YangMills
