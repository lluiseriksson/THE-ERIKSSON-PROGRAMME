/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.KP.RootedCatalanIdentityProof

/-!
# La mejora Catalan exacta pedida por `RootedLeafSummation`

`rootedChildCount_factorialTreeSum_normalized_le_centralBinom` acota la forma
normalizada por `(2n).choose n` y su docstring anticipa: *"A future Catalan
closure must improve this parent-map profile loss by the rooted plane-tree
enumeration factor."*  Este archivo entrega esa mejora: la cantidad es
exactamente `catalan n` — mismo `spanningTrees (⊤)`, mismo
`rootedChildCount`, misma normalización, sin cambio de clase de árboles.
-/

open Nat Finset SimpleGraph
open scoped BigOperators

namespace YangMills.KP

/-- **La mejora exacta**: la forma normalizada no solo está acotada por el
binomial central — es exactamente `catalan n`. -/
theorem rootedChildCount_factorialTreeSum_normalized_eq_catalan (n : ℕ) :
    ((n : ℝ) + 1) * (((n + 1).factorial : ℝ))⁻¹ *
        (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ))
      = (catalan n : ℝ) := by
  have h := rootedChildFactorialCatalanIdentity_holds n
  unfold RootedChildFactorialCatalanIdentity
    rootedChildFactorialTreeSumNormalized rootedChildFactorialTreeSum at h
  exact h

/-- Forma de desigualdad: sustituto directo del consumo de
`..._le_centralBinom`, con la constante mejorada en el factor `n + 1`
(`(n + 1) * catalan n = (2n).choose n`). -/
theorem rootedChildCount_factorialTreeSum_normalized_le_catalan (n : ℕ) :
    ((n : ℝ) + 1) * (((n + 1).factorial : ℝ))⁻¹ *
        (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ))
      ≤ (catalan n : ℝ) :=
  le_of_eq (rootedChildCount_factorialTreeSum_normalized_eq_catalan n)

end YangMills.KP

#print axioms YangMills.KP.rootedChildCount_factorialTreeSum_normalized_eq_catalan
#print axioms YangMills.KP.rootedChildCount_factorialTreeSum_normalized_le_catalan
