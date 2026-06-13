/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.RG.CouplingFlowBridge
import YangMills.RG.CouplingFlow
import YangMills.Paper.ClusteringToGap

/-!
# End-to-end UV conditional: cluster bound + coupling decay ⟹ lattice mass gap

`docs/UV-SINGLE-SCALE-PLAN.md`.  This file closes the loop: it composes
the gauge-RG coupling-flow bridge (`RG/CouplingFlowBridge`) with the
banked mass-gap assembly (`YangMills.lattice_mass_gap_of_per_scale_uv`,
ledger Add. 19) into a single conditional theorem whose hypotheses are
exactly the two genuinely-analytic Bałaban inputs:

* `hRpoly` — the **renormalization-group remainder activity bound** at
  distance `t` and scale `k`, `|R_{t,k}| ≤ A·e^{−c₀t}·g_k^{κ₀}` (spatial
  exponential decay × the running-coupling power; the Dimock
  cluster-expansion-with-holes output, `docs/BALABAN-SOURCE-BOUNDS.md`);
* `hg` — the **coupling-flow decay** `g_k ≤ C·rᵏ` (the irrelevant
  mechanism; cf. `RG/CouplingFlow`).

From these (plus the theorem-fed IR clustering bound and the
covariance-as-scale-sum structure), the **lattice mass gap** follows:
`∃ gap > 0, |covIR t + covUV t| ≤ const·e^{−gap·t}`.  Every step here is
oracle-clean; the only unproved content is the two carried hypotheses —
the §6.3 obligation, now reduced to its faithful form.

**Source.** Bałaban CMP 122-II (the `R`-term polymer bound); Dimock
I/II/III (the cluster expansion); strategy/framing Lluis Eriksson
(ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

open YangMills

/-- **End-to-end UV conditional**: the renormalization-group remainder
activity bound `|R_{t,k}| ≤ A·e^{−c₀t}·g_k^{κ₀}` together with the
coupling-flow decay `g_k ≤ C·rᵏ` (and the theorem-fed IR bound + the
covariance-as-scale-sum structure) imply the **lattice mass gap**.
Composes `coupling_flow_bridge` (applied per distance `t`, with amplitude
`A·e^{−c₀t}`, turning `g_k^{κ₀}` into `C^{κ₀}·rᵏ`) with the banked
`lattice_mass_gap_of_per_scale_uv`.  This is the §6.3 UV obligation in
its faithful, fully-assembled conditional form: the two carried
hypotheses `hRpoly` and `hg` are exactly the Bałaban cluster-expansion
and coupling-flow inputs. -/
theorem lattice_mass_gap_of_cluster_and_coupling
    (covIR covUV : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ) (g : ℕ → ℝ)
    {C1 ε c0 A C r κ₀ : ℝ}
    (hε : 0 < ε) (hc0 : 0 < c0) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hr0 : 0 < r) (hr1 : r < 1) (hκ : 1 ≤ κ₀)
    (hg0 : ∀ k, 0 ≤ g k) (hg : ∀ k, g k ≤ C * r ^ k)
    (hIRbound : ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hcovUV : ∀ t : ℕ, covUV t = ∑ k ∈ Finset.range (nsc t), Rsc t k)
    (hRpoly : ∀ t k : ℕ,
      |Rsc t k| ≤ A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV t|
        ≤ (C1 + A * C ^ κ₀ * (1 - r)⁻¹) * Real.exp (-(gap * (t : ℝ))) := by
  have hRsc : ∀ t k : ℕ,
      |Rsc t k| ≤ (A * C ^ κ₀ * Real.exp (-(c0 * (t : ℝ)))) * r ^ k := by
    intro t k
    have hb := coupling_flow_bridge g (fun j => Rsc t j)
      (mul_nonneg hA (Real.exp_pos _).le) hC hr0 hr1.le hκ hg0 hg
      (fun j => hRpoly t j) k
    calc |Rsc t k|
        ≤ A * Real.exp (-(c0 * (t : ℝ))) * C ^ κ₀ * r ^ k := hb
      _ = (A * C ^ κ₀ * Real.exp (-(c0 * (t : ℝ)))) * r ^ k := by ring
  exact lattice_mass_gap_of_per_scale_uv covIR covUV Rsc nsc C1 (A * C ^ κ₀)
    ε c0 r hε hc0 (mul_nonneg hA (Real.rpow_nonneg hC κ₀)) hr0.le hr1
    hIRbound hcovUV hRsc

/-- **End-to-end UV conditional with the coupling discharged** (tighter
form): the same conclusion as `lattice_mass_gap_of_cluster_and_coupling`,
but the coupling-flow *decay* hypothesis `hg` is replaced by the more
fundamental **logistic RG recursion** `g_{k+1} ≤ r·g_k·(1−β·g_k)` (the
canonically-irrelevant β-function step; `0 ≤ β·g_k ≤ 1` small field).
The decay `g_k ≤ g_0·rᵏ` is derived internally (`logistic_geometric_decay`),
so the coupling input is now the RG recursion itself.  From the cluster
activity bound + the coupling recursion (+ IR bound + covariance
scale-sum), the **lattice mass gap** follows. -/
theorem lattice_mass_gap_of_cluster_and_logistic_coupling
    (covIR covUV : ℕ → ℝ) (Rsc : ℕ → ℕ → ℝ) (nsc : ℕ → ℕ) (g : ℕ → ℝ)
    {C1 ε c0 A r β κ₀ : ℝ}
    (hε : 0 < ε) (hc0 : 0 < c0) (hA : 0 ≤ A)
    (hr0 : 0 < r) (hr1 : r < 1) (hκ : 1 ≤ κ₀)
    (hg0 : ∀ k, 0 ≤ g k) (hb : ∀ k, 0 ≤ β * g k ∧ β * g k ≤ 1)
    (hrec : ∀ k, g (k + 1) ≤ r * g k * (1 - β * g k))
    (hIRbound : ∀ k : ℕ, |covIR k| ≤ C1 * Real.exp (-(ε * (k : ℝ))))
    (hcovUV : ∀ t : ℕ, covUV t = ∑ k ∈ Finset.range (nsc t), Rsc t k)
    (hRpoly : ∀ t k : ℕ,
      |Rsc t k| ≤ A * Real.exp (-(c0 * (t : ℝ))) * g k ^ κ₀) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ t : ℕ,
      |covIR t + covUV t|
        ≤ (C1 + A * g 0 ^ κ₀ * (1 - r)⁻¹) * Real.exp (-(gap * (t : ℝ))) := by
  have hg : ∀ k, g k ≤ g 0 * r ^ k := fun k => by
    rw [mul_comm]; exact logistic_geometric_decay g hr0.le hg0 hb hrec k
  exact lattice_mass_gap_of_cluster_and_coupling covIR covUV Rsc nsc g
    hε hc0 hA (hg0 0) hr0 hr1 hκ hg0 hg hIRbound hcovUV hRpoly

end YangMills.RG
