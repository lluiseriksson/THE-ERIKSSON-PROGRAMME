/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceStratifiedGaugeMass

/-!
# Norm bound for the CMP99 stratified precision

The finite stratified mass is bounded by the sum of its absolute scalar
weights whenever every restricted average is a contraction.  Keeping this
operator-algebra lemma independent of the dependent physical dictionaries
avoids duplicating the proof at each source realization.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

universe u v w

/-- Norm of the finite stratified source mass. -/
theorem norm_cmp99SourceStratifiedGaugeMass_le_sum_abs
    {n : ℕ}
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E]
    (F : Fin n → Type v) (H : Fin n → Type w)
    [∀ r, NormedAddCommGroup (F r)] [∀ r, InnerProductSpace ℝ (F r)]
    [∀ r, CompleteSpace (F r)]
    [∀ r, NormedAddCommGroup (H r)] [∀ r, InnerProductSpace ℝ (H r)]
    [∀ r, CompleteSpace (H r)]
    (Qprime : ∀ r, E →L[ℝ] F r)
    (stratumRestriction : ∀ r, F r →L[ℝ] H r)
    (weight : Fin n → ℝ)
    (hcontract : ∀ r, ‖(stratumRestriction r).comp (Qprime r)‖ ≤ 1) :
    ‖cmp99SourceStratifiedGaugeMass F H Qprime stratumRestriction weight‖ ≤
      ∑ r : Fin n, |weight r| := by
  let A : ∀ r : Fin n, E →L[ℝ] H r :=
    fun r => (stratumRestriction r).comp (Qprime r)
  change ‖∑ r : Fin n, weight r • ((A r).adjoint.comp (A r))‖ ≤ _
  calc
    ‖∑ r : Fin n, weight r • ((A r).adjoint.comp (A r))‖ ≤
        ∑ r : Fin n, ‖weight r • ((A r).adjoint.comp (A r))‖ :=
      norm_sum_le _ _
    _ = ∑ r : Fin n, |weight r| * ‖A r‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [norm_smul, ContinuousLinearMap.norm_adjoint_comp_self,
        Real.norm_eq_abs]
      ring
    _ ≤ ∑ r : Fin n, |weight r| := by
      apply Finset.sum_le_sum
      intro r _
      have hsq : ‖A r‖ ^ 2 ≤ 1 := by
        nlinarith [hcontract r, norm_nonneg (A r)]
      simpa using mul_le_mul_of_nonneg_left hsq (abs_nonneg (weight r))

/-- Norm of the complete stratified precision. -/
theorem norm_cmp99SourceStratifiedGaugePrecision_le
    {n : ℕ}
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E]
    (F : Fin n → Type v) (H : Fin n → Type w)
    [∀ r, NormedAddCommGroup (F r)] [∀ r, InnerProductSpace ℝ (F r)]
    [∀ r, CompleteSpace (F r)]
    [∀ r, NormedAddCommGroup (H r)] [∀ r, InnerProductSpace ℝ (H r)]
    [∀ r, CompleteSpace (H r)]
    (covariantLaplacian : E →L[ℝ] E)
    (Qprime : ∀ r, E →L[ℝ] F r)
    (stratumRestriction : ∀ r, F r →L[ℝ] H r)
    (weight : Fin n → ℝ)
    (hcontract : ∀ r, ‖(stratumRestriction r).comp (Qprime r)‖ ≤ 1) :
    ‖cmp99SourceStratifiedGaugePrecision F H covariantLaplacian Qprime
        stratumRestriction weight‖ ≤
      ‖covariantLaplacian‖ + ∑ r : Fin n, |weight r| := by
  rw [cmp99SourceStratifiedGaugePrecision]
  exact (norm_add_le _ _).trans (add_le_add_right
    (norm_cmp99SourceStratifiedGaugeMass_le_sum_abs
      F H Qprime stratumRestriction weight hcontract) _)

end

end YangMills.RG
