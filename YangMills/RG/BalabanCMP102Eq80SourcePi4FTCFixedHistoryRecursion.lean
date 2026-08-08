/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCConnectedDomainLeaf

/-!
# The full FTC recursion with a literal fixed derivative history

This is the structural bridge between the generic FTC tree and the physical
connected-domain recursion.  A history records every fiber already entered.
When it is empty, the terminal leaf is excluded; once it is nonempty, every
descendant leaf is retained.

The theorem below proves that this recursion is exactly the nondecoupled
remainder at the root and exactly the full expansion below an active fiber.
-/

namespace YangMills.RG

noncomputable section

/-- Literal FTC recursion parameterized by its reverse-chronological history. -/
noncomputable def cmp116FixedHistoryFTCRecursion
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) :
    List (D × ℝ) → (D → ℝ) → List D → ℝ
  | [], _sigma, [] => 0
  | history@(_ :: _), sigma, [] =>
      cmp116FixedWeakeningCoordinateDerivatives f history sigma
  | history, sigma, d :: tail =>
      cmp116FixedHistoryFTCRecursion f history
          (Function.update sigma d 0) tail +
        ∫ t in (0 : ℝ)..1,
          cmp116FixedHistoryFTCRecursion f ((d, t) :: history)
            (Function.update sigma d t) tail

/-- A fixed history describes exactly the relevant projection of the literal
FTC expansion tree. -/
theorem cmp116FixedHistoryFTCRecursion_eq
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) (history : List (D × ℝ))
    (sigma : D → ℝ) (remaining : List D) :
    cmp116FixedHistoryFTCRecursion f history sigma remaining =
      match history with
      | [] =>
          CMP116FTCExpansionTree.nondecoupledRemainder
            (cmp116RealWeakeningFTCExpansionTree f sigma remaining)
      | _ :: _ =>
          (cmp116RealWeakeningFTCExpansionTree
            (cmp116FixedWeakeningCoordinateDerivatives f history)
            sigma remaining).expansionSum := by
  induction remaining generalizing history sigma with
  | nil =>
      cases history <;>
        simp [cmp116FixedHistoryFTCRecursion,
          cmp116RealWeakeningFTCExpansionTree,
          CMP116FTCExpansionTree.expansionSum,
          CMP116FTCExpansionTree.nondecoupledRemainder]
  | cons d tail ih =>
      cases history with
      | nil =>
          simp only [cmp116FixedHistoryFTCRecursion,
            cmp116RealWeakeningFTCExpansionTree]
          rw [ih [] (Function.update sigma d 0)]
          simp_rw [ih [(d, _)] (Function.update sigma d _)]
          rfl
      | cons p history =>
          simp only [cmp116FixedHistoryFTCRecursion,
            cmp116RealWeakeningFTCExpansionTree]
          rw [ih (p :: history) (Function.update sigma d 0)]
          simp_rw [ih ((d, _) :: p :: history)
            (Function.update sigma d _)]
          rfl

/-- At the root, the fixed-history recursion is the exact nondecoupled
remainder. -/
theorem cmp116FixedHistoryFTCRecursion_nil
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) (sigma : D → ℝ) (remaining : List D) :
    cmp116FixedHistoryFTCRecursion f [] sigma remaining =
      CMP116FTCExpansionTree.nondecoupledRemainder
        (cmp116RealWeakeningFTCExpansionTree f sigma remaining) := by
  simpa using
    cmp116FixedHistoryFTCRecursion_eq f [] sigma remaining

end

end YangMills.RG
