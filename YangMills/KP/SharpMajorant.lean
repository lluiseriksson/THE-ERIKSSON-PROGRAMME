/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Criterion

/-!
# Sharp KP, step 4 — the depth-recursion majorant (the analytic half)

`docs/SHARP-KP-PLAN.md` §2 Route A: the sharp Kotecký–Preiss bound proceeds
by decomposing pinned clusters into rooted trees of bounded depth, whose
generating sums obey the recursion

  `Φ₀(c) = 1`,   `Φ_{D+1}(c) = exp( ∑_{c' ≁ c} ‖z(c')‖ · Φ_D(c') )`.

This file provides that majorant and its **complete analytic theory** under
the KP criterion — no uniform-`A` anywhere:

* `kpMajorant` — the recursion;
* `one_le_kpMajorant` / `kpMajorant_nonneg` — positivity;
* `kpMajorant_mono` — monotone in depth (the limit exists);
* **`kpMajorant_le_exp`** — the key bound `Φ_D(c) ≤ e^{a(c)}` for every
  depth, by induction with the criterion absorbing each shell.

What remains for the sharp endpoint is the **combinatorial half**: the
identity/inequality `(pinned cluster sums) ≤ Φ_D`-limits (shell
decomposition of pinned clusters into rooted trees).  With it,
`kpMajorant_le_exp` immediately yields
`∑ pinned weights ≤ e^{a(c)}`-form bounds — volume-uniform when composed
with `connectedLatticePolymerSystem_kpCriterion_volumeUniform`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

open Classical in
/-- The **depth-`D` KP majorant**: the generating bound for rooted
tree-clusters of depth ≤ `D` pinned at a polymer. -/
noncomputable def kpMajorant (P : PolymerSystem) [Fintype P.Polymer] :
    ℕ → P.Polymer → ℝ
  | 0, _ => 1
  | D + 1, c => Real.exp (∑ c' ∈ Finset.univ.filter (fun c' => P.incomp c c'),
      ‖P.activity c'‖ * kpMajorant P D c')

open Classical in
lemma kpMajorant_zero (P : PolymerSystem) [Fintype P.Polymer]
    (c : P.Polymer) : kpMajorant P 0 c = 1 := rfl

open Classical in
lemma kpMajorant_succ (P : PolymerSystem) [Fintype P.Polymer]
    (D : ℕ) (c : P.Polymer) :
    kpMajorant P (D + 1) c
      = Real.exp (∑ c' ∈ Finset.univ.filter (fun c' => P.incomp c c'),
          ‖P.activity c'‖ * kpMajorant P D c') := rfl

open Classical in
/-- The majorant is at least `1` at every depth. -/
lemma one_le_kpMajorant (P : PolymerSystem) [Fintype P.Polymer] :
    ∀ (D : ℕ) (c : P.Polymer), 1 ≤ kpMajorant P D c := by
  intro D
  induction D with
  | zero => intro c; rw [kpMajorant_zero]
  | succ D ih =>
      intro c
      rw [kpMajorant_succ]
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      refine Real.exp_le_exp.mpr ?_
      refine Finset.sum_nonneg fun c' _ => ?_
      exact mul_nonneg (norm_nonneg _)
        (le_trans zero_le_one (ih c'))

open Classical in
lemma kpMajorant_nonneg (P : PolymerSystem) [Fintype P.Polymer]
    (D : ℕ) (c : P.Polymer) : 0 ≤ kpMajorant P D c :=
  le_trans zero_le_one (one_le_kpMajorant P D c)

open Classical in
/-- The majorant is monotone in the depth. -/
lemma kpMajorant_mono (P : PolymerSystem) [Fintype P.Polymer] :
    ∀ (D : ℕ) (c : P.Polymer), kpMajorant P D c ≤ kpMajorant P (D + 1) c := by
  intro D
  induction D with
  | zero =>
      intro c
      rw [kpMajorant_zero]
      exact one_le_kpMajorant P 1 c
  | succ D ih =>
      intro c
      rw [kpMajorant_succ, kpMajorant_succ]
      refine Real.exp_le_exp.mpr (Finset.sum_le_sum fun c' _ => ?_)
      exact mul_le_mul_of_nonneg_left (ih c') (norm_nonneg _)

open Classical in
/-- **THE KEY BOUND (analytic half of sharp KP):** under the Kotecký–Preiss
criterion, the depth-`D` majorant is bounded by `e^{a(c)}` for **every**
depth — the criterion absorbs each shell exactly once, with no uniform
majorant of the weights anywhere. -/
theorem kpMajorant_le_exp (P : PolymerSystem) [Fintype P.Polymer]
    {a : P.Polymer → ℝ} (h : KPCriterion P a) :
    ∀ (D : ℕ) (c : P.Polymer), kpMajorant P D c ≤ Real.exp (a c) := by
  intro D
  induction D with
  | zero =>
      intro c
      rw [kpMajorant_zero]
      exact Real.one_le_exp (h.1 c)
  | succ D ih =>
      intro c
      rw [kpMajorant_succ]
      refine Real.exp_le_exp.mpr ?_
      calc ∑ c' ∈ Finset.univ.filter (fun c' => P.incomp c c'),
            ‖P.activity c'‖ * kpMajorant P D c'
          ≤ ∑ c' ∈ Finset.univ.filter (fun c' => P.incomp c c'),
              ‖P.activity c'‖ * Real.exp (a c') :=
            Finset.sum_le_sum fun c' _ =>
              mul_le_mul_of_nonneg_left (ih c') (norm_nonneg _)
        _ ≤ a c := h.2 c

end YangMills.KP
