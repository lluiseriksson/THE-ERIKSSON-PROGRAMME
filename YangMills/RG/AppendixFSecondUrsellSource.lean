/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpSourceMajorant
import YangMills.KP.KPBound

/-!
# Appendix F: finite source-facing tree majorants for the second Ursell layer

This module adds the first source-independent coefficientwise step behind the
Appendix-F `H#` estimate: the exact fixed-union absolute term is dominated by
the corresponding finite sum over spanning trees of the incompatibility graph.

This is only Penrose tree-graph bookkeeping for a finite fiber.  It does not
prove Dimock's leaf summation, the pointwise `K#` estimate (642)/(644), the
source `H#` estimate F.1/(636), any smallness condition, or any Yang--Mills
raw activity bound.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- The finite tree-graph majorant for the fixed-union `H#` coefficient.  It
has the same target fiber and factorial normalization as
`appendixFHoleHsharpAbsTerm`, but replaces the absolute Ursell coefficient by
the number of spanning trees of the tuple incompatibility graph. -/
noncomputable def appendixFHoleHsharpTreeTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
          (fun X => omegaClusterUnion HF zK X = Y),
      ∑ _T ∈ KP.spanningTrees
          (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
        ∏ i, ‖(omegaHolePolymerSystem HF zK).activity (X i)‖

/-- Penrose tree-graph domination for the exact finite fixed-union
second-Ursell coefficient. -/
theorem appendixFHoleHsharpAbsTerm_le_treeTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (Y : Finset (Cube d L))
    (n : ℕ) :
    appendixFHoleHsharpAbsTerm HF zK Y n ≤
      appendixFHoleHsharpTreeTerm HF zK Y n := by
  classical
  unfold appendixFHoleHsharpAbsTerm appendixFHoleHsharpTreeTerm
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum ?_
  intro X _hX
  let P := omegaHolePolymerSystem HF zK
  let trees := KP.spanningTrees (KP.incompGraph P X)
  let weight : ℝ := ∏ i, ‖P.activity (X i)‖
  have hweight_nonneg : 0 ≤ weight := by
    exact Finset.prod_nonneg fun i _ => norm_nonneg _
  have hU := KP.abs_ursell_le_card_spanningTrees P X
  have hUreal :
      |((KP.ursell P X : ℤ) : ℝ)| ≤ (trees.card : ℝ) := by
    exact_mod_cast hU
  calc
    |((KP.ursell P X : ℤ) : ℝ)| * weight
        ≤ (trees.card : ℝ) * weight :=
          mul_le_mul_of_nonneg_right hUreal hweight_nonneg
    _ =
        ∑ _T ∈ trees, weight := by
          rw [Finset.sum_const, nsmul_eq_mul]

end YangMills.RG
