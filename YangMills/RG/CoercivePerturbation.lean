/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.GaugePrecision

/-!
# Coercivity under operator-norm perturbations

This module isolates the source-independent Hilbert-space estimate used by the
P4 gauge-precision route: a coercive quadratic form remains coercive after a
bounded perturbation, with the coercivity constant reduced by the operator-norm
budget.  The infinite-sum version is intentionally abstract; future
gauge-fixed Hessian work can feed it with the concrete multiscale perturbation
budget, without packaging that budget as a physical theorem.

This file does not define the Yang--Mills Hessian, covariance, covariance root,
or raw CMP116 activity.  It is only deterministic functional analysis.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- A continuous linear operator is coercive with constant `c` when its
quadratic form dominates `c * ‖x‖²` for every vector. -/
def IsCoerciveCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (c : ℝ) : Prop :=
  ∀ x, c * ‖x‖ ^ 2 ≤ inner ℝ x (A x)

/-- The quadratic form of a bounded perturbation is controlled by its operator
norm. -/
theorem abs_inner_apply_le_opNorm_mul_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E) (x : E) :
    |inner ℝ x (B x)| ≤ ‖B‖ * ‖x‖ ^ 2 := by
  have hinner : |inner ℝ x (B x)| ≤ ‖x‖ * ‖B x‖ :=
    abs_real_inner_le_norm x (B x)
  have hB : ‖B x‖ ≤ ‖B‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm B x
  have hmul : ‖x‖ * ‖B x‖ ≤ ‖x‖ * (‖B‖ * ‖x‖) :=
    mul_le_mul_of_nonneg_left hB (norm_nonneg x)
  calc
    |inner ℝ x (B x)| ≤ ‖x‖ * ‖B x‖ := hinner
    _ ≤ ‖x‖ * (‖B‖ * ‖x‖) := hmul
    _ = ‖B‖ * ‖x‖ ^ 2 := by ring

/-- Upper one-sided quadratic-form control from an operator-norm budget. -/
theorem inner_apply_le_of_opNorm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E) {δ : ℝ} (hB : ‖B‖ ≤ δ) (x : E) :
    inner ℝ x (B x) ≤ δ * ‖x‖ ^ 2 := by
  have habs := abs_inner_apply_le_opNorm_mul_norm_sq B x
  have hbudget :
      ‖B‖ * ‖x‖ ^ 2 ≤ δ * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hB (sq_nonneg ‖x‖)
  exact (le_of_abs_le habs).trans hbudget

/-- Lower one-sided quadratic-form control from an operator-norm budget. -/
theorem neg_opNorm_budget_mul_norm_sq_le_inner_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E) {δ : ℝ} (hB : ‖B‖ ≤ δ) (x : E) :
    -δ * ‖x‖ ^ 2 ≤ inner ℝ x (B x) := by
  have habs := abs_inner_apply_le_opNorm_mul_norm_sq B x
  have hbudget :
      ‖B‖ * ‖x‖ ^ 2 ≤ δ * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hB (sq_nonneg ‖x‖)
  calc
    -δ * ‖x‖ ^ 2 = -(δ * ‖x‖ ^ 2) := by ring
    _ ≤ -(‖B‖ * ‖x‖ ^ 2) := neg_le_neg hbudget
    _ ≤ inner ℝ x (B x) := neg_le_of_abs_le habs

/-- Adding a perturbation whose operator norm is at most `δ` reduces the
coercivity constant by at most `δ`. -/
theorem isCoercive_add_of_opNorm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : E →L[ℝ] E) {c δ : ℝ}
    (hA : IsCoerciveCLM A c) (hB : ‖B‖ ≤ δ) :
    IsCoerciveCLM (A + B) (c - δ) := by
  intro x
  have hsum :
      c * ‖x‖ ^ 2 + (-δ * ‖x‖ ^ 2) ≤
        inner ℝ x (A x) + inner ℝ x (B x) :=
    add_le_add (hA x) (neg_opNorm_budget_mul_norm_sq_le_inner_apply B hB x)
  calc
    (c - δ) * ‖x‖ ^ 2
        = c * ‖x‖ ^ 2 + (-δ * ‖x‖ ^ 2) := by ring
    _ ≤ inner ℝ x (A x) + inner ℝ x (B x) := hsum
    _ = inner ℝ x ((A + B) x) := by
      rw [ContinuousLinearMap.add_apply, inner_add_right]

/-- Subtracting a perturbation whose operator norm is at most `δ` reduces the
coercivity constant by at most `δ`. -/
theorem isCoercive_sub_of_opNorm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : E →L[ℝ] E) {c δ : ℝ}
    (hA : IsCoerciveCLM A c) (hB : ‖B‖ ≤ δ) :
    IsCoerciveCLM (A - B) (c - δ) := by
  intro x
  have hBupper : inner ℝ x (B x) ≤ δ * ‖x‖ ^ 2 :=
    inner_apply_le_of_opNorm_le B hB x
  have hquad :
      c * ‖x‖ ^ 2 - δ * ‖x‖ ^ 2 ≤
        inner ℝ x (A x) - inner ℝ x (B x) := by
    nlinarith [hA x, hBupper]
  calc
    (c - δ) * ‖x‖ ^ 2
        = c * ‖x‖ ^ 2 - δ * ‖x‖ ^ 2 := by ring
    _ ≤ inner ℝ x (A x) - inner ℝ x (B x) := hquad
    _ = inner ℝ x ((A - B) x) := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_right]

/-- Infinite perturbation-budget closure: if each perturbation has operator norm
bounded by a summable scalar budget, then subtracting their `tsum` reduces the
coercivity constant by at most the scalar `tsum`. -/
theorem isCoercive_sub_tsum_of_norm_budget
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (Sigma : ι → E →L[ℝ] E) (δ : ι → ℝ) {c : ℝ}
    (hA : IsCoerciveCLM A c)
    (hδ : Summable δ)
    (hSigmaδ : ∀ i, ‖Sigma i‖ ≤ δ i) :
    IsCoerciveCLM (A - ∑' i, Sigma i) (c - ∑' i, δ i) := by
  have hnormSigma : Summable fun i => ‖Sigma i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg (Sigma i)) hSigmaδ hδ
  have htsumBudget : ‖∑' i, Sigma i‖ ≤ ∑' i, δ i :=
    (norm_tsum_le_tsum_norm hnormSigma).trans
      (Summable.tsum_le_tsum hSigmaδ hnormSigma hδ)
  exact isCoercive_sub_of_opNorm_le A (∑' i, Sigma i) hA htsumBudget

/-- The adjoint block-average mass is coercive with the semidefinite constant
`0`.  This is a small sanity check that the abstract predicate matches the
existing `qMassCLM` quadratic-form API. -/
theorem isCoerciveCLM_qMassCLM_zero
    {d L N' : ℕ} {V : Type*}
    [NeZero L] [NeZero N']
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype (ConcreteEdge d (L * N'))] [Fintype (ConcreteEdge d N')]
    (s : ℝ) :
    IsCoerciveCLM (qMassCLM (d := d) (V := V) s L N') 0 := by
  intro A
  simpa using qMassCLM_psd (d := d) (V := V) s L N' A

/-- Existing block-Poincare plus `qMassCLM` coercivity, repackaged in the
generic `IsCoerciveCLM` predicate for downstream perturbation budgeting. -/
theorem isCoerciveCLM_add_qMassCLM_of_blockPoincare
    {d L N' : ℕ} {V : Type*}
    [NeZero L] [NeZero N']
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype (ConcreteEdge d (L * N'))] [Fintype (ConcreteEdge d N')]
    (K : FineBondHilbert d L N' V →L[ℝ] FineBondHilbert d L N' V)
    (s : ℝ) {a CP : ℝ}
    (ha : 0 ≤ a) (hCP : 0 < CP)
    (hKnonneg :
      ∀ A : FineBondHilbert d L N' V, 0 ≤ inner ℝ A (K A))
    (hPoincare :
      ∀ A : FineBondHilbert d L N' V,
        ‖A‖ ^ 2 ≤
          CP * (inner ℝ A (K A) +
            ‖scaledLinAvgCLM (d := d) (V := V) s L N' A‖ ^ 2)) :
    IsCoerciveCLM
      (K + a • qMassCLM (d := d) (V := V) s L N')
      (min 1 a / CP) := by
  intro A
  exact
    coercive_add_qMassCLM_of_blockPoincare
      (d := d) (V := V) K s ha hCP hKnonneg hPoincare A

end YangMills.RG
