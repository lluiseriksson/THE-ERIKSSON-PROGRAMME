/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFSecondUrsellSource

/-!
# Appendix F: weighted finite tree terms for the second Ursell layer

This module factors the finite Penrose tree majorant into two source-facing
pieces: a scalar activity size and a purely geometric polymer weight.  The
main theorem is only finite algebra: if every second-gas activity is bounded
by `epsilon * w`, then the exact finite tree term is bounded by
`epsilon^(n+1)` times the weighted tree term.

No Dimock leaf summation, CMP116 estimate, smallness condition, continuum
construction, or Clay conclusion is proved here.  The future analytic theorem
must still bound the weighted tree term itself.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open scoped BigOperators

variable {d L : ℕ} [NeZero L]

/-- Weighted finite tree majorant for the fixed-union `H#` coefficient.  It
has the same fixed-union fiber and factorial normalization as
`appendixFHoleHsharpTreeTerm`, but replaces the norm of each activity by an
external nonnegative weight `w`. -/
noncomputable def appendixFHoleHsharpWeightedTreeTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
          (fun X => omegaClusterUnion HF zK X = Y),
      ∑ _T ∈ KP.spanningTrees
          (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
        ∏ i, w (X i)

/-- The weighted tree term is nonnegative whenever the weight is nonnegative. -/
theorem appendixFHoleHsharpWeightedTreeTerm_nonneg
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (n : ℕ)
    (hw : ∀ Q, 0 ≤ w Q) :
    0 ≤ appendixFHoleHsharpWeightedTreeTerm HF zK w Y n := by
  classical
  unfold appendixFHoleHsharpWeightedTreeTerm
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun X _ =>
      Finset.sum_nonneg fun _T _ =>
        Finset.prod_nonneg fun i _ => hw (X i))

/-- Order-zero normalization: the factorial is `1` and the vertex product is
the single weight.  This lemma deliberately leaves the finite set of spanning
trees explicit; the source theorem decides how to evaluate or bound it. -/
@[simp] theorem appendixFHoleHsharpWeightedTreeTerm_zero
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L)) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y 0 =
      ∑ X ∈ (Finset.univ :
          Finset (Fin 1 → OmegaPolymerType HF zK)).filter
            (fun X => omegaClusterUnion HF zK X = Y),
        ∑ _T ∈ KP.spanningTrees
            (KP.incompGraph (omegaHolePolymerSystem HF zK) X),
          w (X 0) := by
  classical
  simp [appendixFHoleHsharpWeightedTreeTerm]

/-- Finite activity-size extraction for the source-facing tree majorant.  If
each second-gas activity is bounded by `epsilon * w`, then a tuple of size
`n+1` contributes the scalar factor `epsilon^(n+1)`, leaving the weighted tree
term for the geometry/leaf-summation step. -/
theorem appendixFHoleHsharpTreeTerm_le_scaled_weightedTreeTerm
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (n : ℕ)
    (epsilon : ℝ)
    (hε : 0 ≤ epsilon)
    (hw : ∀ Q, 0 ≤ w Q)
    (hactivity :
      ∀ Q : OmegaPolymerType HF zK,
        ‖zK Q.val‖ ≤ epsilon * w Q) :
    appendixFHoleHsharpTreeTerm HF zK Y n ≤
      epsilon ^ (n + 1) *
        appendixFHoleHsharpWeightedTreeTerm HF zK w Y n := by
  classical
  let P := omegaHolePolymerSystem HF zK
  let fiber : Finset (Fin (n + 1) → OmegaPolymerType HF zK) :=
    (Finset.univ :
        Finset (Fin (n + 1) → OmegaPolymerType HF zK)).filter
      (fun X => omegaClusterUnion HF zK X = Y)
  let epow : ℝ := epsilon ^ (n + 1)
  have hprod :
      ∀ X : Fin (n + 1) → OmegaPolymerType HF zK,
        ∏ i, ‖P.activity (X i)‖ ≤ epow * ∏ i, w (X i) := by
    intro X
    have htarget_nonneg :
        0 ≤ ∏ i : Fin (n + 1), epsilon * w (X i) := by
      exact Finset.prod_nonneg fun i _ => mul_nonneg hε (hw (X i))
    have hpoint :
        ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
          ‖P.activity (X i)‖ ≤ epsilon * w (X i) := by
      intro i _hi
      simpa [P, omegaHolePolymerSystem] using hactivity (X i)
    calc
      ∏ i, ‖P.activity (X i)‖
          ≤ ∏ i : Fin (n + 1), epsilon * w (X i) :=
            Finset.prod_le_prod
              (fun i _ => norm_nonneg (P.activity (X i))) hpoint
      _ = epow * ∏ i, w (X i) := by
            simp [epow, Finset.prod_mul_distrib]
  have htrees :
      ∀ X : Fin (n + 1) → OmegaPolymerType HF zK,
        (∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
            ∏ i, ‖P.activity (X i)‖) ≤
          epow *
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, w (X i) := by
    intro X
    calc
      (∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
          ∏ i, ‖P.activity (X i)‖)
          ≤ ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              epow * ∏ i, w (X i) :=
            Finset.sum_le_sum fun _T _hT => hprod X
      _ = epow *
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, w (X i) := by
            rw [Finset.mul_sum]
  have hfiber :
      (∑ X ∈ fiber,
          ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
            ∏ i, ‖P.activity (X i)‖) ≤
        epow *
          ∑ X ∈ fiber,
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, w (X i) := by
    calc
      (∑ X ∈ fiber,
          ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
            ∏ i, ‖P.activity (X i)‖)
          ≤ ∑ X ∈ fiber,
              epow *
                ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
                  ∏ i, w (X i) :=
            Finset.sum_le_sum fun X _hX => htrees X
      _ = epow *
          ∑ X ∈ fiber,
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, w (X i) := by
            rw [Finset.mul_sum]
  have hfinal :
      (((n + 1).factorial : ℝ))⁻¹ *
          (∑ X ∈ fiber,
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, ‖P.activity (X i)‖) ≤
        epsilon ^ (n + 1) *
          ((((n + 1).factorial : ℝ))⁻¹ *
            (∑ X ∈ fiber,
              ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
                ∏ i, w (X i))) := by
    calc
      (((n + 1).factorial : ℝ))⁻¹ *
          (∑ X ∈ fiber,
            ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
              ∏ i, ‖P.activity (X i)‖)
          ≤ (((n + 1).factorial : ℝ))⁻¹ *
              (epow *
                ∑ X ∈ fiber,
                  ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
                    ∏ i, w (X i)) :=
            mul_le_mul_of_nonneg_left hfiber (by positivity)
      _ =
        epsilon ^ (n + 1) *
          ((((n + 1).factorial : ℝ))⁻¹ *
            (∑ X ∈ fiber,
              ∑ _T ∈ KP.spanningTrees (KP.incompGraph P X),
                ∏ i, w (X i))) := by
            simp [epow, mul_left_comm]
  simpa [appendixFHoleHsharpTreeTerm, appendixFHoleHsharpWeightedTreeTerm,
    fiber, P, epow] using hfinal

/-- Algebraic reassociation of the weighted tree transfer.  If the weighted
tree term has a bound `Croot * decay * Cleaf^n`, then extracting the activity
size `epsilon` from each of the `n+1` vertices gives the source-normal
factorization with one root factor and `n` leaf factors. -/
theorem appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_bound
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (n : ℕ)
    (epsilon Croot Cleaf decay : ℝ)
    (hε : 0 ≤ epsilon)
    (hw : ∀ Q, 0 ≤ w Q)
    (hactivity :
      ∀ Q : OmegaPolymerType HF zK,
        ‖zK Q.val‖ ≤ epsilon * w Q)
    (hweighted :
      appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
        Croot * decay * Cleaf ^ n) :
    appendixFHoleHsharpTreeTerm HF zK Y n ≤
      (Croot * epsilon * decay) * (Cleaf * epsilon) ^ n := by
  have hscaled :=
    appendixFHoleHsharpTreeTerm_le_scaled_weightedTreeTerm
      HF zK w Y n epsilon hε hw hactivity
  have hpow_nonneg : 0 ≤ epsilon ^ (n + 1) := pow_nonneg hε _
  have hweighted_scaled :
      epsilon ^ (n + 1) *
          appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
        epsilon ^ (n + 1) * (Croot * decay * Cleaf ^ n) :=
    mul_le_mul_of_nonneg_left hweighted hpow_nonneg
  refine hscaled.trans ?_
  refine hweighted_scaled.trans_eq ?_
  ring

/-- Source-shaped geometric consumer for the weighted tree estimate.  The
future leaf-summation theorem should supply `hleaf`; this theorem performs
only the finite scalar extraction and algebraic rearrangement. -/
theorem appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_geometric
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (epsilon Croot Cleaf κ κ₀ : ℝ)
    (hε : 0 ≤ epsilon)
    (hw : ∀ Q, 0 ≤ w Q)
    (hactivity :
      ∀ Q : OmegaPolymerType HF zK,
        ‖zK Q.val‖ ≤ epsilon * w Q)
    (hleaf :
      ∀ (P : OmegaPolymerType HF zK) n,
        appendixFHoleHsharpWeightedTreeTerm HF zK w P.val n ≤
          Croot *
            Real.exp
              (-(polymerClusterResidualRate κ κ₀ *
                ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))) *
            Cleaf ^ n) :
    ∀ (P : OmegaPolymerType HF zK) n,
      appendixFHoleHsharpTreeTerm HF zK P.val n ≤
        (Croot * epsilon *
          Real.exp
            (-(polymerClusterResidualRate κ κ₀ *
              ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ)))) *
          (Cleaf * epsilon) ^ n := by
  intro P n
  exact appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_bound
    HF zK w P.val n epsilon Croot Cleaf
    (Real.exp
      (-(polymerClusterResidualRate κ κ₀ *
        ((discreteModifiedMetric HF P.val + 1 : ℕ) : ℝ))))
    hε hw hactivity (hleaf P n)

end YangMills.RG
