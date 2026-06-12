/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Expansion
import YangMills.KP.Convergence

/-!
# KP2b capstone — the single-polymer Mayer identity, conditional on Target A

This file **composes** the verified bridges into the first non-trivial case of the Mayer
identity `Ξ = exp(clusterSum)`: for a system with a single polymer of activity `z`
(`‖z‖ < 1`), `clusterSum = log(1 + z)` and `Ξ = exp(clusterSum)` — *granting* Target A's
complete-graph recurrence.

The pieces it assembles (all already verified):
* `ursellComplete_closed_form` — Target A back-half: recurrence ⟹ `φ(K_{n+1}) = (−1)ⁿ·n!`.
* `mayer_log_series_complex` — `∑ₙ (−1)ⁿ·zⁿ⁺¹/(n+1) = log(1+z)`.
* `partition_singleton` — `Ξ({()}) = 1+z`.
* factorial cancellation `n!/(n+1)! = 1/(n+1)`; `Complex.exp_log` (`1+z ≠ 0`).

The recurrence enters only as the explicit hypothesis `hrec` — no axiom.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.KP

open scoped BigOperators

/-- A polymer system with a **single polymer** (`Unit`) of complex activity `z`,
self-incompatible by the hard core.  Its incompatibility structure is identical to
`completeSystem`, so its Ursell values are the complete-graph values `ursellComplete`. -/
def singlePolymerSystem (z : ℂ) : PolymerSystem where
  Polymer := Unit
  incomp _ _ := True
  incomp_symm _ _ _ := trivial
  incomp_self _ := trivial
  activity _ := z

instance (z : ℂ) : Fintype (singlePolymerSystem z).Polymer :=
  (inferInstance : Fintype Unit)

instance (z : ℂ) : Unique (singlePolymerSystem z).Polymer :=
  (inferInstance : Unique Unit)

@[simp] lemma singlePolymerSystem_activity (z : ℂ) (u : Unit) :
    (singlePolymerSystem z).activity u = z := rfl

/-- The Ursell coefficient in the single-polymer system equals the complete-graph value:
`ursell` ignores activities and the incompatibility structure matches `completeSystem`. -/
lemma ursell_singlePolymerSystem (z : ℂ) {n : ℕ} (X : Fin n → Unit) :
    ursell (singlePolymerSystem z) X = ursellComplete n := by
  rw [Subsingleton.elim X (fun _ => ())]
  rfl

/-- **Single-polymer cluster sum (conditional on Target A).**  Granting the complete-graph
recurrence `hrec`, the cluster sum of a one-polymer system with activity `z` (`‖z‖ < 1`)
is `log(1 + z)`. -/
theorem clusterSum_singlePolymer (z : ℂ) (h : ‖z‖ < 1)
    (hrec : ∀ n : ℕ, 1 ≤ n → ursellComplete (n + 1) = -(n : ℤ) * ursellComplete n) :
    clusterSum (singlePolymerSystem z) = Complex.log (1 + z) := by
  have hclosed := ursellComplete_closed_form hrec
  rw [← (mayer_log_series_complex h).tsum_eq]
  unfold clusterSum
  refine tsum_congr (fun n => ?_)
  rw [Fintype.sum_unique]
  simp only [singlePolymerSystem_activity, ursell_singlePolymerSystem,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hclosed n]
  push_cast [Nat.factorial_succ]
  have hfac : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- **Single-polymer Mayer identity `Ξ = exp(clusterSum)` (conditional on Target A).**
Composing `clusterSum_singlePolymer` (`clusterSum = log(1+z)`) with `partition_singleton`
(`Ξ({()}) = 1+z`) and `exp_log` (valid since `‖z‖ < 1 ⟹ 1+z ≠ 0`), the partition function
of a one-polymer system equals `exp(clusterSum)` — the first non-trivial case of the
Mayer cluster-expansion identity, holding the moment Target A's recurrence is proved. -/
theorem partition_eq_exp_clusterSum_singlePolymer (z : ℂ) (h : ‖z‖ < 1)
    (hrec : ∀ n : ℕ, 1 ≤ n → ursellComplete (n + 1) = -(n : ℤ) * ursellComplete n) :
    partition (singlePolymerSystem z) ({()} : Finset (singlePolymerSystem z).Polymer)
      = Complex.exp (clusterSum (singlePolymerSystem z)) := by
  have hz : (1 : ℂ) + z ≠ 0 := by
    intro hzero
    have hz1 : z = -1 := by linear_combination hzero
    rw [hz1] at h; simp at h
  rw [clusterSum_singlePolymer z h hrec, Complex.exp_log hz]
  exact (partition_singleton (singlePolymerSystem z) ()).trans
    (by rw [singlePolymerSystem_activity])

end YangMills.KP
