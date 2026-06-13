/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib

/-!
# The coupling-flow bridge (gauge-RG campaign, UV audit-gap closer)

`docs/BALABAN-SOURCE-BOUNDS.md` §2, `docs/UV-SINGLE-SCALE-PLAN.md` §3.

The audit of the §6.3 UV obligation (ledger Add. 47) established that
Bałaban does **not** state the surrogate `|R_k| ≤ M·rᵏ` consumed by
`Paper.uv_geometric_summation`.  His faithful bound is the
polymer-localized `|R_k| ≤ A·g_k^{κ₀}` (CMP 122-II / [III] §2, eqs
2.31[III], 1.100) in terms of the running coupling `g_k`, and the
surrogate follows **only** under the extra coupling-flow decay
`g_k ≤ C·rᵏ`.

This file proves exactly that logical transfer, and nothing more.  It
deliberately does **not** encode the cluster expansion, the Dimock
fluctuation integral, or the large-field "holes" lemma — those are the
open months-scale analytic core.  It isolates the two genuinely-unproved
inputs as explicit hypotheses (`hg`, `hpoly`), so the assembly can
depend on the surrogate `|R_k| ≤ M·rᵏ` while the Clay-distance audit
stays honest about what remains open.

**Source.** Bałaban CMP 122-II Thm 1 / [III] §2; the bridge is the
elementary `rpow` transfer.  Strategy/framing: Lluis Eriksson
(ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

/-- **Coupling-flow bridge** (UV audit-gap closer): if the scale-`k`
remainder obeys Bałaban's polymer bound `|R_k| ≤ A·g_k^{κ₀}` (in terms of
the running coupling `g_k ≥ 0`, exponent `κ₀ ≥ 1`) and the coupling flows
with geometric decay `g_k ≤ C·rᵏ` (`0 < r ≤ 1`), then the surrogate
geometric bound `|R_k| ≤ (A·C^{κ₀})·rᵏ` holds.  This is the *only*
logical step connecting the faithful Bałaban bound to the surrogate
`|R_k| ≤ M·rᵏ` consumed by `uv_geometric_summation`; the two
analytically-hard facts are exposed as the hypotheses `hpoly`
(polymer/cluster bound) and `hg` (coupling-flow decay). -/
theorem coupling_flow_bridge (g R : ℕ → ℝ) {A C r κ₀ : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hr0 : 0 < r) (hr1 : r ≤ 1) (hκ : 1 ≤ κ₀)
    (hg0 : ∀ k, 0 ≤ g k) (hg : ∀ k, g k ≤ C * r ^ k)
    (hpoly : ∀ k, |R k| ≤ A * g k ^ κ₀) :
    ∀ k, |R k| ≤ A * C ^ κ₀ * r ^ k := by
  intro k
  have hrk0 : 0 < r ^ k := pow_pos hr0 k
  have hrk1 : r ^ k ≤ 1 := pow_le_one₀ hr0.le hr1
  -- the κ₀-power of the coupling decays at least as `C^{κ₀}·rᵏ`
  have hgk : g k ^ κ₀ ≤ C ^ κ₀ * r ^ k := by
    have step1 : g k ^ κ₀ ≤ (C * r ^ k) ^ κ₀ :=
      Real.rpow_le_rpow (hg0 k) (hg k) (by linarith)
    have step2 : (C * r ^ k) ^ κ₀ = C ^ κ₀ * (r ^ k) ^ κ₀ :=
      Real.mul_rpow hC hrk0.le
    have step3 : (r ^ k) ^ κ₀ ≤ r ^ k :=
      calc (r ^ k) ^ κ₀ ≤ (r ^ k) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hrk0 hrk1 hκ
        _ = r ^ k := Real.rpow_one _
    calc g k ^ κ₀ ≤ (C * r ^ k) ^ κ₀ := step1
      _ = C ^ κ₀ * (r ^ k) ^ κ₀ := step2
      _ ≤ C ^ κ₀ * r ^ k := by
          apply mul_le_mul_of_nonneg_left step3; positivity
  calc |R k| ≤ A * g k ^ κ₀ := hpoly k
    _ ≤ A * (C ^ κ₀ * r ^ k) := mul_le_mul_of_nonneg_left hgk hA
    _ = A * C ^ κ₀ * r ^ k := by ring

end YangMills.RG
