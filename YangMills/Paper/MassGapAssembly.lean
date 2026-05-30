/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Honest conditional formalization of §6.1 (telescoping) and §7 (mass-gap assembly)

Second batch of formalized pieces of the Eriksson paper ("Exponential Clustering and
Mass Gap for 4D SU(N) Lattice Yang–Mills", §6–§7).  As in `CouplingControl.lean`,
the genuinely hard, imported inputs are carried as **hypotheses, never axioms**.

* `telescoping` — the algebraic skeleton of the **multiscale telescoping identity**
  (§6.1, Prop. 6.1).  The paper obtains it from the law of total covariance along the
  σ-algebra chain `Σ_{a₀} ⊇ … ⊇ Σ_{a*}`; its purely algebraic core is the telescoping
  sum `S 0 = S n + Σ_{k<n} (S k − S (k+1))`, which we prove outright (no hypotheses).

* `mass_gap_bound` — the **assembly of the mass-gap bound** (§7, Theorem 7.1).  Given
    - the infrared/terminal exponential-clustering bound `|covIR| ≤ C₁ e^{−m* t}` (§5),
    - the ultraviolet-suppression bound `|covUV| ≤ C₂ e^{−c₀ t}` (§6.3), and
    - the telescoping decomposition `cov = covIR + covUV`,
  we prove `|cov| ≤ (C₁+C₂) e^{−min(m*,c₀) t}` — exponential clustering with rate
  `m = min(m*, c₀) > 0`.  Here `t` stands for `|x|/a*`.

## What this does and does NOT establish

`mass_gap_bound` machine-checks the §7 *assembly logic*: that the two exponential
bounds combine into one with the worse rate.  It does **not** prove those bounds —
the terminal clustering (§5, which rests on the KP input of "Paper [1]") and the
single-scale UV error (§6.2, which rests on Balaban's propagator/large-field
estimates).  Those are the imported, unclosed content; here they are visible
hypotheses.  And none of this touches OS1 / O(4) covariance — so it remains, by the
paper's own statement, a *conditional lattice* result, not the Clay theorem.
See `ROADMAP.md §4` and `FOUNDATIONS.md`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.Paper

open scoped BigOperators

/-- **Multiscale telescoping identity (§6.1, algebraic core).**
For any scale-indexed quantity `S` (think: the correlator with scales `0..k` coarse-
grained), the original-scale value equals the terminal value plus the sum of the
single-scale increments. This is the law-of-total-covariance telescoping of Prop. 6.1
stripped to its algebra; proved outright. -/
theorem telescoping (S : ℕ → ℝ) (n : ℕ) :
    S 0 = S n + ∑ k ∈ Finset.range n, (S k - S (k + 1)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    linarith [ih]

/-- **Mass-gap bound assembly (§7, Theorem 7.1) — honest conditional theorem.**
Given the infrared clustering bound and the ultraviolet suppression bound (the
contents of §5 and §6.3, taken here as hypotheses) together with the telescoping
decomposition, the full correlator decays exponentially with rate `min(m*, c₀)`. -/
theorem mass_gap_bound
    (cov covIR covUV C1 C2 mstar c0 t : ℝ)
    (ht : 0 ≤ t)
    (hdec : cov = covIR + covUV)
    (hIR : |covIR| ≤ C1 * Real.exp (-(mstar * t)))
    (hUV : |covUV| ≤ C2 * Real.exp (-(c0 * t))) :
    |cov| ≤ (C1 + C2) * Real.exp (-(min mstar c0 * t)) := by
  have hEpos1 : 0 < Real.exp (-(mstar * t)) := Real.exp_pos _
  have hEpos2 : 0 < Real.exp (-(c0 * t)) := Real.exp_pos _
  -- The prefactors are forced nonnegative by the bounds themselves.
  have hC1 : 0 ≤ C1 := by
    by_contra h; push_neg at h
    have h1 : C1 * Real.exp (-(mstar * t)) < 0 := mul_neg_of_neg_of_pos h hEpos1
    have h2 : 0 ≤ C1 * Real.exp (-(mstar * t)) := le_trans (abs_nonneg covIR) hIR
    linarith
  have hC2 : 0 ≤ C2 := by
    by_contra h; push_neg at h
    have h1 : C2 * Real.exp (-(c0 * t)) < 0 := mul_neg_of_neg_of_pos h hEpos2
    have h2 : 0 ≤ C2 * Real.exp (-(c0 * t)) := le_trans (abs_nonneg covUV) hUV
    linarith
  -- Replacing each rate by the worse rate only increases the exponential.
  have hEIR : Real.exp (-(mstar * t)) ≤ Real.exp (-(min mstar c0 * t)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left mstar c0, ht]
  have hEUV : Real.exp (-(c0 * t)) ≤ Real.exp (-(min mstar c0 * t)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_right mstar c0, ht]
  calc |cov| = |covIR + covUV| := by rw [hdec]
    _ ≤ |covIR| + |covUV| := abs_add_le _ _
    _ ≤ C1 * Real.exp (-(mstar * t)) + C2 * Real.exp (-(c0 * t)) := add_le_add hIR hUV
    _ ≤ C1 * Real.exp (-(min mstar c0 * t)) + C2 * Real.exp (-(min mstar c0 * t)) :=
        add_le_add (mul_le_mul_of_nonneg_left hEIR hC1)
                   (mul_le_mul_of_nonneg_left hEUV hC2)
    _ = (C1 + C2) * Real.exp (-(min mstar c0 * t)) := by ring
