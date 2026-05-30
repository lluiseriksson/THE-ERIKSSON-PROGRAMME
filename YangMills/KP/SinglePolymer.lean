/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.KP.Expansion
import YangMills.KP.Convergence

/-!
# KP2b capstone — the single-polymer Mayer identity, conditional on Target A

This file **composes** the verified bridges into the first non-trivial case of the Mayer
identity `Ξ = exp(clusterSum)`: for a system with a single polymer of activity `z`
(`‖z‖ < 1`), `clusterSum = log(1 + z)` — *granting* Target A's complete-graph recurrence.

The pieces it assembles (all already verified):
* `ursellComplete_closed_form` — Target A back-half: recurrence ⟹ `φ(K_{n+1}) = (−1)ⁿ·n!`.
* `mayer_log_series_complex` — `∑ₙ (−1)ⁿ·zⁿ⁺¹/(n+1) = log(1+z)`.
* factorial cancellation `n!/(n+1)! = 1/(n+1)`.

Result: `clusterSum (singlePolymerSystem z) = log(1+z)`, hence (with `partition_singleton`,
`Ξ({X}) = 1+z`) the single-polymer identity `Ξ = exp(clusterSum)` holds the moment Target
A is closed.  The recurrence enters only as the explicit hypothesis `hrec` — no axiom.

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

/-- **Single-polymer Mayer identity (conditional on Target A).**  Granting the
complete-graph recurrence `hrec`, the cluster sum of a one-polymer system with activity
`z` (`‖z‖ < 1`) is `log(1 + z)`.  Together with `partition_singleton` this is the `n = 1`
case of `Ξ = exp(clusterSum)` — unconditional once Target A's `ursellComplete_recurrence`
is proved. -/
theorem clusterSum_singlePolymer (z : ℂ) (h : ‖z‖ < 1)
    (hrec : ∀ n : ℕ, 1 ≤ n → ursellComplete (n + 1) = -(n : ℤ) * ursellComplete n) :
    clusterSum (singlePolymerSystem z) = Complex.log (1 + z) := by
  have hclosed := ursellComplete_closed_form hrec
  rw [← (mayer_log_series_complex h).tsum_eq]
  unfold clusterSum
  refine tsum_congr (fun n => ?_)
  -- Inner sum over `Fin (n+1) → Unit` (a `Unique` type) collapses to the single tuple.
  rw [Fintype.sum_unique]
  simp only [singlePolymerSystem_activity, ursell_singlePolymerSystem,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Now: ((n+1)!)⁻¹ * (ursellComplete (n+1) : ℂ) * z^(n+1) = (-1)^n * z^(n+1)/(n+1).
  rw [hclosed n]
  push_cast [Nat.factorial_succ]
  have hfac : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp