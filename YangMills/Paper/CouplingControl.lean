/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# Honest conditional formalization of the coupling-control induction (Paper §4)

This is the **first formalized piece of the Eriksson paper** ("Exponential
Clustering and Mass Gap for 4D SU(N) Lattice Yang–Mills", §4, Prop. 4.1), encoded
as an *explicitly conditional* theorem.

The inputs the paper imports from Balaban's framework are carried here as
**hypotheses, NOT axioms** (avoiding the "wrong-axiom trap" of `FOUNDATIONS.md`):

* the discrete β-function recursion on the inverse-square couplings `u k = g_k^{-2}`:
  `u (k+1) = u k + b₀ + r k`;
* the Cauchy/analyticity remainder bound `|r k| ≤ C / u k`  (= `C·g_k²`,
  Prop. 4.1, Eq. (10)–(11));
* asymptotic freedom of the leading coefficient `b₀ > 0`;
* a small-coupling start `U₀ ≤ u 0` with the closure condition `C / U₀ < b₀ / 2`.

Under these we prove the paper's Prop. 4.1 conclusion: the inverse-square coupling
grows at least linearly,

  `u k ≥ u 0 + k · (b₀ / 2)`,

i.e. `g_k → 0` (asymptotic freedom) with constants uniform in `k`, and the flow
never leaves the small-coupling regime (`U₀ ≤ u k` for all k).

## What this does and does NOT establish

It machine-checks that the **induction/bookkeeping of §4 is correct GIVEN Balaban's
analyticity inputs**.  It does **not** prove those inputs — the uniform analyticity
radius `R*`, the value `b₀ = 11N/(48π²)`, the polymer/large-field bounds.  Those are
the genuinely hard, imported content that the literature has not fully closed; here
they are visible hypotheses.  This theorem is therefore a faithful, oracle-clean
statement of the *conditional logic* of §4, and nothing more.  See `ROADMAP.md` (M3)
and `FOUNDATIONS.md` (the wrong-axiom trap).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.Paper

/-- **Coupling control (Paper §4, Prop. 4.1) — honest conditional theorem.**

Given Balaban's β-function recursion and the analyticity remainder bound as
explicit hypotheses, the inverse-square coupling `u k = g_k^{-2}` grows at least
linearly in the RG step `k`. -/
theorem coupling_control
    (u r : ℕ → ℝ) (b0 C U0 : ℝ)
    (hb0 : 0 < b0) (hU0 : 0 < U0)
    (hclose : C / U0 < b0 / 2)
    (hu0 : U0 ≤ u 0)
    (hrec : ∀ k, u (k + 1) = u k + b0 + r k)
    (hr : ∀ k, |r k| ≤ C / u k) :
    ∀ k : ℕ, u 0 + (k : ℝ) * (b0 / 2) ≤ u k := by
  have hb2 : (0 : ℝ) ≤ b0 / 2 := by linarith
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    -- The flow stays in the small-coupling regime: U₀ ≤ u 0 ≤ u n.
    have hnn : (0 : ℝ) ≤ (n : ℝ) * (b0 / 2) := mul_nonneg (Nat.cast_nonneg n) hb2
    have hun : U0 ≤ u n := by linarith
    have hupos : 0 < u n := lt_of_lt_of_le hU0 hun
    -- The remainder cannot overwhelm half of b₀ in the small-coupling regime.
    have hClt : C < (b0 / 2) * U0 := (div_lt_iff₀ hU0).mp hclose
    have hmono : (b0 / 2) * U0 ≤ (b0 / 2) * u n := mul_le_mul_of_nonneg_left hun hb2
    have hCun : C / u n < b0 / 2 := by
      rw [div_lt_iff₀ hupos]; linarith
    -- Hence r n ≥ -(C / u n) > -(b₀/2).
    have habs : -(C / u n) ≤ r n := (abs_le.mp (hr n)).1
    have hexp : ((n + 1 : ℕ) : ℝ) * (b0 / 2) = (n : ℝ) * (b0 / 2) + b0 / 2 := by
      push_cast; ring
    rw [hexp]
    have hrecn := hrec n
    linarith
