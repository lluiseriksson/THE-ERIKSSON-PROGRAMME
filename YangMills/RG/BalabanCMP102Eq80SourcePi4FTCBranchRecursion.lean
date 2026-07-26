/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCConnectedDomainRecursion

/-!
# A recursion exposing the active part of the literal FTC tree

The physical connected-domain recursion has the same branching structure as
the literal FTC tree, but its terminal leaves are localized Faà di Bruno
coefficients.  This file isolates that common structure before any physical
identification of the leaves.

`active = false` discards the unique branch containing no derivative and is
therefore exactly `nondecoupledRemainder`.  Once a fiber has been entered,
`active = true` and the complete expansion of every descendant is retained.
This distinction is essential: replacing a fiber by its own nondecoupled
remainder would incorrectly discard mixed terms whose later coordinates all
follow base branches.
-/

namespace YangMills.RG

noncomputable section

/-- Recursively retain either the complete real weakening tree (`active`) or
only those branches that contain at least one integrated derivative
(`active = false`). -/
noncomputable def cmp116RealWeakeningFTCActiveRecursion
    {D : Type*} [DecidableEq D]
    (active : Bool) (f : (D → ℝ) → ℝ) (s : D → ℝ) :
    List D → ℝ
  | [] => if active then f s else 0
  | d :: tail =>
      cmp116RealWeakeningFTCActiveRecursion active f
          (Function.update s d 0) tail +
        ∫ t in (0 : ℝ)..1,
          cmp116RealWeakeningFTCActiveRecursion true
            (cmp116RealWeakeningCoordinateDerivative f d t)
            (Function.update s d t) tail

/-- The active recursion is definitionally faithful to the two relevant
projections of the literal FTC tree. -/
theorem cmp116RealWeakeningFTCActiveRecursion_eq
    {D : Type*} [DecidableEq D]
    (active : Bool) (f : (D → ℝ) → ℝ) (s : D → ℝ)
    (L : List D) :
    cmp116RealWeakeningFTCActiveRecursion active f s L =
      if active then
        (cmp116RealWeakeningFTCExpansionTree f s L).expansionSum
      else
        (cmp116RealWeakeningFTCExpansionTree f s L).nondecoupledRemainder := by
  induction L generalizing active f s with
  | nil =>
      cases active <;>
        simp [cmp116RealWeakeningFTCActiveRecursion,
          cmp116RealWeakeningFTCExpansionTree,
          CMP116FTCExpansionTree.expansionSum,
          CMP116FTCExpansionTree.nondecoupledRemainder]
  | cons d tail ih =>
      cases active with
      | false =>
          simp only [cmp116RealWeakeningFTCActiveRecursion,
            cmp116RealWeakeningFTCExpansionTree,
            Bool.false_eq_true, ↓reduceIte]
          rw [ih false]
          simp_rw [ih true]
          rfl
      | true =>
          simp only [cmp116RealWeakeningFTCActiveRecursion,
            cmp116RealWeakeningFTCExpansionTree, ↓reduceIte]
          rw [ih true]
          simp_rw [ih true]
          rfl

/-- With no derivative selected yet, the active recursion is exactly the
nondecoupled remainder. -/
theorem cmp116RealWeakeningFTCActiveRecursion_false
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) (s : D → ℝ) (L : List D) :
    cmp116RealWeakeningFTCActiveRecursion false f s L =
      (cmp116RealWeakeningFTCExpansionTree f s L).nondecoupledRemainder := by
  simpa using
    cmp116RealWeakeningFTCActiveRecursion_eq false f s L

/-- After the first derivative has been selected, the active recursion retains
the complete descendant expansion. -/
theorem cmp116RealWeakeningFTCActiveRecursion_true
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) (s : D → ℝ) (L : List D) :
    cmp116RealWeakeningFTCActiveRecursion true f s L =
      (cmp116RealWeakeningFTCExpansionTree f s L).expansionSum := by
  simpa using
    cmp116RealWeakeningFTCActiveRecursion_eq true f s L

end

end YangMills.RG
