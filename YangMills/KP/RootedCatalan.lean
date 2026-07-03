/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.KP.RootedLeafSummation
import Mathlib.Combinatorics.Enumerative.Catalan

/-!
# Rooted child-factorial Catalan identity

This module names the exact Catalan replacement point for the existing
`4^n` rooted child-factorial tree summation.

The proposition in this file is kept as a named interface, while
`YangMills.KP.RootedCatalanIdentityProof` proves it unconditionally from the
ported Catalan closure.

Oracle target for the lemmas in this file:
`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.KP

open SimpleGraph
open scoped BigOperators

/-- The unnormalized rooted child-factorial sum over complete-graph spanning
trees on `Fin (n+1)`. -/
noncomputable def rootedChildFactorialTreeSum (n : ℕ) : ℝ :=
  ∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
    ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ)

/-- The exact second-Ursell normalization applied to
`rootedChildFactorialTreeSum`. -/
noncomputable def rootedChildFactorialTreeSumNormalized (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (((n + 1).factorial : ℝ))⁻¹ *
    rootedChildFactorialTreeSum n

/-- Statement of the exact Catalan identity.  Keeping it as a named proposition
makes downstream theorem statements stable; the unconditional proof is supplied
in `YangMills.KP.RootedCatalanIdentityProof`. -/
def RootedChildFactorialCatalanIdentity (n : ℕ) : Prop :=
  rootedChildFactorialTreeSumNormalized n = (catalan n : ℝ)

/-- Inequality consumer form of the exact Catalan identity. -/
theorem rootedChildCount_factorialTreeSum_normalized_le_catalan_of_identity
    (n : ℕ) (hcat : RootedChildFactorialCatalanIdentity n) :
    rootedChildFactorialTreeSumNormalized n ≤ (catalan n : ℝ) := by
  simpa [RootedChildFactorialCatalanIdentity] using le_of_eq hcat

/-- Expansion of the named normalized sum back into the shape consumed by the
existing second-Ursell leaf summation code. -/
theorem rootedChildFactorialTreeSumNormalized_eq_raw (n : ℕ) :
    rootedChildFactorialTreeSumNormalized n =
      ((n : ℝ) + 1) * (((n + 1).factorial : ℝ))⁻¹ *
        (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ)) := by
  rfl

/-- Raw-form Catalan inequality, still explicitly conditional on the exact
combinatorial identity. -/
theorem rootedChildCount_factorialTreeSum_normalized_le_catalan_of_identity_raw
    (n : ℕ) (hcat : RootedChildFactorialCatalanIdentity n) :
    ((n : ℝ) + 1) * (((n + 1).factorial : ℝ))⁻¹ *
        (∑ T ∈ spanningTrees (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v : Fin (n + 1), ((rootedChildCount T v).factorial : ℝ))
      ≤ (catalan n : ℝ) := by
  simpa [rootedChildFactorialTreeSumNormalized,
    rootedChildFactorialTreeSum] using
      rootedChildCount_factorialTreeSum_normalized_le_catalan_of_identity n hcat

end YangMills.KP
