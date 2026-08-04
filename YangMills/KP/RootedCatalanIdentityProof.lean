/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.

# Unconditional closure of the rooted child-factorial Catalan identity

This file connects the repository-facing proposition
`RootedChildFactorialCatalanIdentity`, defined in `YangMills.KP.RootedCatalan`,
with the natural-number identity proved in `YangMills.KP.RootedCatalanBridge`:

  `∑ T ∈ spanningTrees ⊤, ∏ v, (rootedChildCount T v)! = n ! * catalan n`

and concludes, for every `n`,

  `rootedChildFactorialTreeSumNormalized n = (catalan n : ℝ)`.
-/
import YangMills.KP.RootedCatalan
import YangMills.KP.RootedCatalanBridge

open Nat Finset SimpleGraph
open scoped BigOperators

namespace YangMills.KP

/-- The exact Catalan identity of the program, unconditionally. -/
theorem rootedChildFactorialCatalanIdentity_holds (n : ℕ) :
    RootedChildFactorialCatalanIdentity n := by
  unfold RootedChildFactorialCatalanIdentity
    rootedChildFactorialTreeSumNormalized rootedChildFactorialTreeSum
  have h := sum_prod_rootedChildCount_factorial_eq n
  have hsum : (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
      ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ))
      = ((n ! * catalan n : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [hsum]
  have ha : ((n : ℝ) + 1) ≠ 0 := by
    have h2 : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by rw [Nat.cast_add_one]
    rw [h2]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hb : ((n ! : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfact : (((n + 1)! : ℕ) : ℝ) = ((n : ℝ) + 1) * ((n ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  rw [Nat.cast_mul, hfact, mul_inv]
  calc ((n : ℝ) + 1) * ((((n : ℝ) + 1)⁻¹ * ((n ! : ℕ) : ℝ)⁻¹)) *
        (((n ! : ℕ) : ℝ) * (catalan n : ℝ))
      = (((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹) *
          ((((n ! : ℕ) : ℝ))⁻¹ * ((n ! : ℕ) : ℝ)) * (catalan n : ℝ) := by ring
    _ = 1 * 1 * (catalan n : ℝ) := by
        rw [mul_inv_cancel₀ ha, inv_mul_cancel₀ hb]
    _ = (catalan n : ℝ) := by ring

/-- Inequality form of the closure, ready for consumers. -/
theorem rootedChildFactorialTreeSumNormalized_le_catalan (n : ℕ) :
    rootedChildFactorialTreeSumNormalized n ≤ (catalan n : ℝ) :=
  le_of_eq (rootedChildFactorialCatalanIdentity_holds n)

end YangMills.KP

#print axioms YangMills.KP.rootedChildFactorialCatalanIdentity_holds
#print axioms YangMills.KP.rootedChildFactorialTreeSumNormalized_le_catalan
