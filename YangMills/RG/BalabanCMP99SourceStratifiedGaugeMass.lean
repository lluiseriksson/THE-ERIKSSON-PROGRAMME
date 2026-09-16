/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGaugePrecision

/-!
# The stratified source mass of CMP99 (3.18)--(3.24)

The printed operator `Q'` is not one terminal block average.  On the stratum
`Lambda_r` it is the order-`r` average `Q'_r`, and its quadratic form is the
sum of the corresponding restricted squared norms.  This file records that
operator algebra before the source-specific regional tower and shell
restrictions are inserted.

The scalar `weight r` is the complete printed coefficient at stratum `r`;
in CMP99 (3.24) it contains both `a_r` and the lattice-spacing power.  Keeping
it as one scalar here prevents an accidental use of the unweighted counting
adjoint.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

noncomputable section

universe u v w

/-- The source-stratified mass

`sum_r weight_r (S_r Q'_r)^* (S_r Q'_r)`,

where `S_r` restricts the order-`r` average to the physical stratum
`Lambda_r`. -/
noncomputable def cmp99SourceStratifiedGaugeMass
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
    (weight : Fin n → ℝ) : E →L[ℝ] E :=
  ∑ r : Fin n,
    weight r •
      (((stratumRestriction r).comp (Qprime r)).adjoint.comp
        ((stratumRestriction r).comp (Qprime r)))

/-- Exact quadratic form of the source-stratified mass. -/
theorem inner_cmp99SourceStratifiedGaugeMass
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
    (weight : Fin n → ℝ) (phi : E) :
    inner ℝ phi
        (cmp99SourceStratifiedGaugeMass F H Qprime stratumRestriction weight
          phi) =
      ∑ r : Fin n,
        weight r * ‖stratumRestriction r (Qprime r phi)‖ ^ 2 := by
  rw [cmp99SourceStratifiedGaugeMass,
    ContinuousLinearMap.sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [ContinuousLinearMap.smul_apply, inner_smul_right,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]
  rfl

/-- Nonnegative stratum weights make the complete printed mass
nonnegative. -/
theorem inner_cmp99SourceStratifiedGaugeMass_nonneg
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
    {weight : Fin n → ℝ} (hweight : ∀ r, 0 ≤ weight r)
    (phi : E) :
    0 ≤ inner ℝ phi
      (cmp99SourceStratifiedGaugeMass F H Qprime stratumRestriction weight
        phi) := by
  rw [inner_cmp99SourceStratifiedGaugeMass]
  exact Finset.sum_nonneg fun r _ => mul_nonneg (hweight r) (sq_nonneg _)

/-- The stratified mass is self-adjoint. -/
theorem cmp99SourceStratifiedGaugeMass_isSymmetric
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
    (weight : Fin n → ℝ) :
    (cmp99SourceStratifiedGaugeMass F H Qprime stratumRestriction weight).IsSymmetric := by
  intro phi psi
  change inner ℝ
      ((∑ r : Fin n,
        weight r •
          (((stratumRestriction r).comp (Qprime r)).adjoint.comp
            ((stratumRestriction r).comp (Qprime r)))) phi) psi =
    inner ℝ phi
      ((∑ r : Fin n,
        weight r •
          (((stratumRestriction r).comp (Qprime r)).adjoint.comp
            ((stratumRestriction r).comp (Qprime r)))) psi)
  simp only [ContinuousLinearMap.sum_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  let A := (stratumRestriction r).comp (Qprime r)
  change inner ℝ (weight r • A.adjoint (A phi)) psi =
    inner ℝ phi (weight r • A.adjoint (A psi))
  rw [inner_smul_left, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  simp

/-- Source-faithful stratified precision `Delta_U + Q'^* a Q'`. -/
noncomputable def cmp99SourceStratifiedGaugePrecision
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
    (weight : Fin n → ℝ) : E →L[ℝ] E :=
  covariantLaplacian +
    cmp99SourceStratifiedGaugeMass F H Qprime stratumRestriction weight

/-- Exact quadratic form of the corrected stratified precision. -/
theorem inner_cmp99SourceStratifiedGaugePrecision
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
    (weight : Fin n → ℝ) (phi : E) :
    inner ℝ phi
        (cmp99SourceStratifiedGaugePrecision F H covariantLaplacian Qprime
          stratumRestriction weight phi) =
      inner ℝ phi (covariantLaplacian phi) +
        ∑ r : Fin n,
          weight r * ‖stratumRestriction r (Qprime r phi)‖ ^ 2 := by
  rw [cmp99SourceStratifiedGaugePrecision,
    ContinuousLinearMap.add_apply, inner_add_right,
    inner_cmp99SourceStratifiedGaugeMass]

/-- Nonnegative printed stratum weights preserve the ambient coercivity
constant for the complete stratified precision. -/
theorem isCoerciveCLM_cmp99SourceStratifiedGaugePrecision
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
    {weight : Fin n → ℝ} (hweight : ∀ r, 0 ≤ weight r)
    {c : ℝ} (hDelta : IsCoerciveCLM covariantLaplacian c) :
    IsCoerciveCLM
      (cmp99SourceStratifiedGaugePrecision F H covariantLaplacian Qprime
        stratumRestriction weight) c := by
  intro phi
  rw [inner_cmp99SourceStratifiedGaugePrecision]
  exact (hDelta phi).trans (le_add_of_nonneg_right
    (Finset.sum_nonneg fun r _ =>
      mul_nonneg (hweight r) (sq_nonneg _)))

/-- Symmetry of the ambient covariant Laplacian passes to the complete
stratified precision. -/
theorem cmp99SourceStratifiedGaugePrecision_isSymmetric
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
    (weight : Fin n → ℝ) (hDelta : covariantLaplacian.IsSymmetric) :
    (cmp99SourceStratifiedGaugePrecision F H covariantLaplacian Qprime
      stratumRestriction weight).IsSymmetric := by
  intro phi psi
  change inner ℝ
      (covariantLaplacian phi +
        cmp99SourceStratifiedGaugeMass F H Qprime stratumRestriction weight phi)
      psi =
    inner ℝ phi
      (covariantLaplacian psi +
        cmp99SourceStratifiedGaugeMass F H Qprime stratumRestriction weight psi)
  rw [inner_add_left, inner_add_right]
  congr 1
  · exact hDelta phi psi
  · exact cmp99SourceStratifiedGaugeMass_isSymmetric F H Qprime
      stratumRestriction weight phi psi

end

end YangMills.RG
