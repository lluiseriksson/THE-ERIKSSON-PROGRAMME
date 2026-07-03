/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.KP.RootedCatalanIdentityProof

/-!
# The exact Catalan improvement requested by `RootedLeafSummation`

`rootedChildCount_factorialTreeSum_normalized_le_centralBinom` bounds the
normalized child-factorial tree sum by `(2n).choose n`, and its docstring
anticipates: *"A future Catalan closure must improve this parent-map profile
loss by the rooted plane-tree enumeration factor."* This module delivers
that improvement: the quantity is exactly `catalan n` — same
`spanningTrees (⊤)`, same `rootedChildCount`, same normalization, no change
of tree class.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

open Nat Finset SimpleGraph
open scoped BigOperators

namespace YangMills.KP

/-- **The exact improvement**: the normalized form is not merely bounded by
the central binomial — it equals `catalan n`. -/
theorem rootedChildCount_factorialTreeSum_normalized_eq_catalan (n : ℕ) :
    ((n : ℝ) + 1) * (((n + 1).factorial : ℝ))⁻¹ *
        (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ))
      = (catalan n : ℝ) := by
  have h := rootedChildFactorialCatalanIdentity_holds n
  unfold RootedChildFactorialCatalanIdentity
    rootedChildFactorialTreeSumNormalized rootedChildFactorialTreeSum at h
  exact h

/-- Inequality form: a drop-in counterpart of `..._le_centralBinom` with the
constant improved by the factor `n + 1`
(`(n + 1) * catalan n = (2n).choose n`). -/
theorem rootedChildCount_factorialTreeSum_normalized_le_catalan (n : ℕ) :
    ((n : ℝ) + 1) * (((n + 1).factorial : ℝ))⁻¹ *
        (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ))
      ≤ (catalan n : ℝ) :=
  le_of_eq (rootedChildCount_factorialTreeSum_normalized_eq_catalan n)

end YangMills.KP
