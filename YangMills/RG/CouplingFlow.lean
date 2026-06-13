/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.RG.CouplingFlowBridge

/-!
# Geometric coupling decay from the irrelevant RG recursion (gauge-RG, UV `hg`)

`docs/BALABAN-SOURCE-BOUNDS.md` §4.  Discharges the coupling-flow
hypothesis `hg : ∀ k, g_k ≤ C·rᵏ` of `coupling_flow_bridge` from the
explicit one-step RG recursion, **for the canonically-irrelevant
mechanism**.

Source: Faria da Veiga–O'Carroll, *Asymptotics for some logistic maps
and the renormalization group*, Physica Scripta 99 (2024) 095262 — the
irrelevant case `λ_{k+1} = r·λ_k·(1 − β·λ_k)` with `0 < r < 1` gives
`λ_{k+1} ≤ r·λ_k`, hence `λ_k ≤ λ_0·rᵏ`; and Goswami (AHP 2019), the
irrelevant remainders `V^{irr}_{k+1} = L^{−2}·V^{irr}_k + O(·²)`, so
`V^{irr}_k ≤ C·rᵏ` with `r = L^{−2}`.

**HONEST SCOPE CAVEAT (critical).**  This geometric decay is the
**irrelevant-operator** mechanism: `r < 1` is the canonical scaling of an
*irrelevant* operator (e.g. `r = L^{−2}`).  The **4D marginal gauge
coupling** of pure Yang–Mills (`α = 1` in the logistic map) decays only
**logarithmically** — `1/λ_0 + βn ≤ 1/λ_n`, i.e. `λ_n ∼ 1/(βn)`
(asymptotic freedom), NOT geometrically.  So applying `g_k ≤ C·rᵏ` to the
*marginal* coupling is FALSE in 4D.  In Bałaban's 4D construction the
geometric remainder contraction `|R_k| ≤ M·rᵏ` comes from the
**irrelevant operators' scaling** (`e^{−κ d(X)}` / `L^{−2k}` factors,
Goswami), with the marginal coupling supplying only a slowly-varying
(logarithmic) prefactor.  The recursion `hrec` below therefore models the
*irrelevant remainder operators*, and `r` is their contraction factor —
not the marginal gauge coupling.  Recorded so the Clay-distance audit
stays honest.

**Source.** Faria da Veiga–O'Carroll 2024; Goswami AHP 2019; Bałaban
CMP 109 (1987).  Strategy/framing: Lluis Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

/-- **Abstract geometric decay**: a nonnegative sequence obeying a
one-step contraction `a_{k+1} ≤ r·a_k` decays as `a_k ≤ r^k·a_0`. -/
theorem geometric_decay_of_contraction (a : ℕ → ℝ) {r : ℝ} (hr0 : 0 ≤ r)
    (ha : ∀ k, 0 ≤ a k) (hrec : ∀ k, a (k + 1) ≤ r * a k) :
    ∀ k, a k ≤ r ^ k * a 0 := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      calc a (n + 1) ≤ r * a n := hrec n
        _ ≤ r * (r ^ n * a 0) := mul_le_mul_of_nonneg_left ih hr0
        _ = r ^ (n + 1) * a 0 := by rw [pow_succ]; ring

/-- **One step of the irrelevant logistic RG recursion is a
contraction**: `r·x·(1 − β·x) ≤ r·x` when `0 ≤ r`, `0 ≤ x`,
`0 ≤ β·x ≤ 1` (the small-field regime). -/
theorem logistic_step_le {r β x : ℝ} (hr0 : 0 ≤ r) (hx : 0 ≤ x)
    (hbx0 : 0 ≤ β * x) (hbx1 : β * x ≤ 1) :
    r * x * (1 - β * x) ≤ r * x := by
  have hrx : 0 ≤ r * x := mul_nonneg hr0 hx
  calc r * x * (1 - β * x) ≤ r * x * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) hrx
    _ = r * x := mul_one _

/-- **Geometric coupling decay from the irrelevant logistic recursion**:
if `g_{k+1} ≤ r·g_k·(1 − β·g_k)` (the canonically-irrelevant RG step,
contraction factor `r`) with `0 ≤ β·g_k ≤ 1`, then `g_k ≤ r^k·g_0`.  See
the module caveat: this is the irrelevant-operator mechanism, NOT the 4D
marginal coupling (which is only logarithmic). -/
theorem logistic_geometric_decay (g : ℕ → ℝ) {r β : ℝ} (hr0 : 0 ≤ r)
    (hg : ∀ k, 0 ≤ g k) (hb : ∀ k, 0 ≤ β * g k ∧ β * g k ≤ 1)
    (hrec : ∀ k, g (k + 1) ≤ r * g k * (1 - β * g k)) :
    ∀ k, g k ≤ r ^ k * g 0 :=
  geometric_decay_of_contraction g hr0 hg
    (fun k => le_trans (hrec k) (logistic_step_le hr0 (hg k) (hb k).1 (hb k).2))

/-- **End-to-end (irrelevant mechanism)**: the irrelevant logistic
coupling recursion together with Bałaban's polymer bound
`|R_k| ≤ A·g_k^{κ₀}` yields the geometric remainder bound
`|R_k| ≤ (A·g_0^{κ₀})·r^k` consumed by `uv_geometric_summation`.
Composition of `logistic_geometric_decay` and `coupling_flow_bridge`;
the two analytically-hard inputs remain the explicit hypotheses `hrec`
(the RG recursion) and `hpoly` (the cluster/polymer bound). -/
theorem remainder_geometric_of_logistic (g R : ℕ → ℝ) {A r β κ₀ : ℝ}
    (hA : 0 ≤ A) (hr0 : 0 < r) (hr1 : r ≤ 1) (hκ : 1 ≤ κ₀)
    (hg : ∀ k, 0 ≤ g k) (hb : ∀ k, 0 ≤ β * g k ∧ β * g k ≤ 1)
    (hrec : ∀ k, g (k + 1) ≤ r * g k * (1 - β * g k))
    (hpoly : ∀ k, |R k| ≤ A * g k ^ κ₀) :
    ∀ k, |R k| ≤ A * g 0 ^ κ₀ * r ^ k := by
  have hg_decay : ∀ k, g k ≤ g 0 * r ^ k := fun k => by
    rw [mul_comm]; exact logistic_geometric_decay g hr0.le hg hb hrec k
  exact coupling_flow_bridge g R hA (hg 0) hr0 hr1 hκ hg hg_decay hpoly

end YangMills.RG
