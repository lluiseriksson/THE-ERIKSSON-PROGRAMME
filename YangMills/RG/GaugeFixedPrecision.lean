/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.CoercivePerturbation
import YangMills.RG.SchurCatalanBudget

/-!
# Gauge-fixed precision coercivity composition

This module composes the already-verified block-Poincare adjoint-mass estimate
with the operator-norm perturbation budget API.  It is a source-independent
Hilbert-space layer for the P4 gauge-fixed precision route:

`Kslice + a Q†Q - Σ`.

The theorems here do not identify `Kslice`, `Q`, or `Σ` with a Yang--Mills
Hessian, gauge slice, block map, or physical self-energy.  Those identifications
remain explicit source obligations for the later physical Hessian layer.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

/-- The positive background precision plus an adjoint block-constraint mass.

This is source-independent notation.  It does not identify `K0` or `Q` with a
particular Yang--Mills Hessian, gauge-fixing operator, or block derivative. -/
noncomputable def gaugeFixedBasePrecisionCLM
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (a : ℝ) :
    E →L[ℝ] E :=
  K0 + a • (Q.adjoint.comp Q)

/-- Base precision minus a summable family of operator corrections.

The `tsum` is totalized; the coercivity theorems below require explicit
summability and norm-budget hypotheses. -/
noncomputable def gaugeFixedPrecisionCLM
    {ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (a : ℝ)
    (Sigma : ι → E →L[ℝ] E) :
    E →L[ℝ] E :=
  gaugeFixedBasePrecisionCLM K0 Q a - ∑' i, Sigma i

/-- Generic `IsCoerciveCLM` wrapper for the block-Poincare adjoint-mass
estimate. -/
theorem isCoerciveCLM_gaugeFixedBasePrecision_of_blockPoincare
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    {a CP : ℝ}
    (ha : 0 ≤ a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2)) :
    IsCoerciveCLM
      (gaugeFixedBasePrecisionCLM K0 Q a)
      (min 1 a / CP) := by
  intro x
  simpa [gaugeFixedBasePrecisionCLM] using
    coercive_add_adjointMass_of_blockPoincare
      K0 Q ha hCP hK0nonneg hPoincare x

/-- Block-Poincare/Hodge coercivity survives subtraction of a summable operator
family, with the explicit residual constant. -/
theorem isCoerciveCLM_gaugeFixedPrecision_of_blockPoincare_normBudget
    {ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 ≤ a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i) :
    IsCoerciveCLM
      (gaugeFixedPrecisionCLM K0 Q a Sigma)
      (min 1 a / CP - ∑' i, δ i) := by
  simpa [gaugeFixedPrecisionCLM] using
    isCoercive_sub_tsum_of_norm_budget
      (gaugeFixedBasePrecisionCLM K0 Q a)
      Sigma δ
      (isCoerciveCLM_gaugeFixedBasePrecision_of_blockPoincare
        K0 Q ha hCP hK0nonneg hPoincare)
      hδ hSigmaδ

/-- The residual coercivity constant is strictly positive when the total
operator budget is below the base constant. -/
theorem gaugeFixedPrecision_coerciveWithPositiveConstant
    {ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    0 < (min 1 a / CP - ∑' i, δ i) ∧
    IsCoerciveCLM
      (gaugeFixedPrecisionCLM K0 Q a Sigma)
      (min 1 a / CP - ∑' i, δ i) := by
  refine ⟨sub_pos.mpr hbudget, ?_⟩
  exact
    isCoerciveCLM_gaugeFixedPrecision_of_blockPoincare_normBudget
      K0 Q Sigma δ ha.le hCP hK0nonneg hPoincare hδ hSigmaδ

/-- Concrete `qMassCLM` specialization of the summable perturbation theorem. -/
theorem isCoerciveCLM_qMass_sub_tsum_of_blockPoincare_normBudget
    {ι : Type*}
    {d L N' : ℕ}
    {V : Type*}
    [NeZero L] [NeZero N']
    [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [Fintype (ConcreteEdge d (L * N'))]
    [Fintype (ConcreteEdge d N')]
    (K0 :
      FineBondHilbert d L N' V →L[ℝ]
        FineBondHilbert d L N' V)
    (s : ℝ)
    (Sigma :
      ι →
        FineBondHilbert d L N' V →L[ℝ]
          FineBondHilbert d L N' V)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 ≤ a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ A : FineBondHilbert d L N' V,
        0 ≤ inner ℝ A (K0 A))
    (hPoincare :
      ∀ A : FineBondHilbert d L N' V,
        ‖A‖ ^ 2 ≤
          CP * (inner ℝ A (K0 A) +
            ‖scaledLinAvgCLM
                (d := d) (V := V) s L N' A‖ ^ 2))
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i) :
    IsCoerciveCLM
      ((K0 + a • qMassCLM (d := d) (V := V) s L N')
        - ∑' i, Sigma i)
      (min 1 a / CP - ∑' i, δ i) := by
  exact
    isCoercive_sub_tsum_of_norm_budget
      (K0 + a • qMassCLM (d := d) (V := V) s L N')
      Sigma δ
      (isCoerciveCLM_add_qMassCLM_of_blockPoincare
        K0 s ha hCP hK0nonneg hPoincare)
      hδ hSigmaδ

/-- Strict positive-constant concrete `qMassCLM` perturbation theorem. -/
theorem qMass_sub_tsum_coerciveWithPositiveConstant_of_blockPoincare_normBudget
    {ι : Type*}
    {d L N' : ℕ}
    {V : Type*}
    [NeZero L] [NeZero N']
    [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [Fintype (ConcreteEdge d (L * N'))]
    [Fintype (ConcreteEdge d N')]
    (K0 :
      FineBondHilbert d L N' V →L[ℝ]
        FineBondHilbert d L N' V)
    (s : ℝ)
    (Sigma :
      ι →
        FineBondHilbert d L N' V →L[ℝ]
          FineBondHilbert d L N' V)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ A : FineBondHilbert d L N' V,
        0 ≤ inner ℝ A (K0 A))
    (hPoincare :
      ∀ A : FineBondHilbert d L N' V,
        ‖A‖ ^ 2 ≤
          CP * (inner ℝ A (K0 A) +
            ‖scaledLinAvgCLM
                (d := d) (V := V) s L N' A‖ ^ 2))
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    0 < (min 1 a / CP - ∑' i, δ i) ∧
    IsCoerciveCLM
      ((K0 + a • qMassCLM (d := d) (V := V) s L N')
        - ∑' i, Sigma i)
      (min 1 a / CP - ∑' i, δ i) := by
  refine ⟨sub_pos.mpr hbudget, ?_⟩
  exact
    isCoerciveCLM_qMass_sub_tsum_of_blockPoincare_normBudget
      K0 s Sigma δ ha.le hCP hK0nonneg hPoincare hδ hSigmaδ

/-- Finite Schur-Catalan lower-bound bridge for one-sided quadratic-form
defect budgets. -/
theorem isCoerciveCLM_sub_finset_of_schurCatalan_blockPoincare
    {ι E F : Type*}
    [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (M epsilon : ι → ℝ)
    (I : Finset ι)
    {a CP : ℝ}
    (ha : 0 ≤ a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hSigma :
      ∀ i, i ∈ I → ∀ x : E,
        inner ℝ x (Sigma i x) ≤
          schurCatalanBudget (M i) (epsilon i) * ‖x‖ ^ 2) :
    IsCoerciveCLM
      (gaugeFixedBasePrecisionCLM K0 Q a -
        ∑ i ∈ I, Sigma i)
      (min 1 a / CP -
        ∑ i ∈ I, schurCatalanBudget (M i) (epsilon i)) := by
  intro x
  have hbase :=
    isCoerciveCLM_gaugeFixedBasePrecision_of_blockPoincare
      K0 Q ha hCP hK0nonneg hPoincare
  have hscalar :=
    schurCatalan_lower_bound_of_finset_budget
      (fun x : E => ‖x‖ ^ 2)
      (fun x : E => inner ℝ x ((gaugeFixedBasePrecisionCLM K0 Q a) x))
      (fun i x => inner ℝ x (Sigma i x))
      M epsilon I hbase hSigma x
  have hinner_sum :
      inner ℝ x (∑ i ∈ I, (Sigma i) x) =
        ∑ i ∈ I, inner ℝ x ((Sigma i) x) := by
    simp [inner_sum]
  simpa [IsCoerciveCLM, ContinuousLinearMap.sub_apply, inner_sub_right,
    ContinuousLinearMap.sum_apply] using
    hscalar.trans_eq (by rw [← hinner_sum])

/-- Strict pointwise positivity from a finite Schur-Catalan defect budget. -/
theorem inner_sub_finset_pos_of_schurCatalan_blockPoincare
    {ι E F : Type*}
    [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (M epsilon : ι → ℝ)
    (I : Finset ι)
    {a CP : ℝ}
    (ha : 0 ≤ a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hSigma :
      ∀ i, i ∈ I → ∀ x : E,
        inner ℝ x (Sigma i x) ≤
          schurCatalanBudget (M i) (epsilon i) * ‖x‖ ^ 2)
    (hbudget :
      (∑ i ∈ I, schurCatalanBudget (M i) (epsilon i))
        < min 1 a / CP) :
    ∀ x : E, x ≠ 0 →
      0 <
        inner ℝ x
          ((gaugeFixedBasePrecisionCLM K0 Q a -
              ∑ i ∈ I, Sigma i) x) := by
  intro x hx
  have hbase :=
    isCoerciveCLM_gaugeFixedBasePrecision_of_blockPoincare
      K0 Q ha hCP hK0nonneg hPoincare
  have hxnorm : 0 < ‖x‖ ^ 2 := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx)
  have hscalar :=
    schurCatalan_coercive_of_finset_budget
      (fun x : E => ‖x‖ ^ 2)
      (fun x : E => inner ℝ x ((gaugeFixedBasePrecisionCLM K0 Q a) x))
      (fun i x => inner ℝ x (Sigma i x))
      M epsilon I hbase hSigma hbudget x hxnorm
  have hinner_sum :
      inner ℝ x (∑ i ∈ I, (Sigma i) x) =
        ∑ i ∈ I, inner ℝ x ((Sigma i) x) := by
    simp [inner_sum]
  have hstrict :
      0 <
        inner ℝ x ((gaugeFixedBasePrecisionCLM K0 Q a) x) -
          inner ℝ x (∑ i ∈ I, (Sigma i) x) :=
    hscalar.trans_eq (by rw [← hinner_sum])
  have hlt :
      inner ℝ x (∑ i ∈ I, (Sigma i) x) <
        inner ℝ x ((gaugeFixedBasePrecisionCLM K0 Q a) x) :=
    sub_pos.mp hstrict
  simpa [ContinuousLinearMap.sub_apply, inner_sub_right,
    ContinuousLinearMap.sum_apply, sub_pos] using hlt

/-- Finite block-Poincare coercivity bridge fed by KP Catalan partial defect
bounds.  This is the concrete quadratic-form consumer of
`schurCatalan_lower_bound_of_catalanMajorantPartial_budget` for the
gauge-fixed precision layer; it does not identify the operator corrections
`Sigma` with a physical Hessian or Appendix-F source term. -/
theorem isCoerciveCLM_sub_finset_of_catalanMajorantPartial_blockPoincare
    {ι E F : Type*}
    [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (M epsilon : ι → ℝ)
    (N : ι → ℕ)
    (I : Finset ι)
    {a CP : ℝ}
    (ha : 0 ≤ a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hM : ∀ i ∈ I, 0 < M i)
    (hepsilon : ∀ i ∈ I, 0 ≤ epsilon i)
    (hsmall : ∀ i ∈ I, 4 * M i ^ 2 * epsilon i ≤ 1)
    (hSigma :
      ∀ i, i ∈ I → ∀ x : E,
        inner ℝ x (Sigma i x) ≤
          YangMills.KP.catalanMajorantPartial (M i) (epsilon i) (N i) *
            ‖x‖ ^ 2) :
    IsCoerciveCLM
      (gaugeFixedBasePrecisionCLM K0 Q a -
        ∑ i ∈ I, Sigma i)
      (min 1 a / CP -
        ∑ i ∈ I, schurCatalanBudget (M i) (epsilon i)) := by
  intro x
  have hbase :=
    isCoerciveCLM_gaugeFixedBasePrecision_of_blockPoincare
      K0 Q ha hCP hK0nonneg hPoincare
  have hscalar :=
    schurCatalan_lower_bound_of_catalanMajorantPartial_budget
      (fun x : E => ‖x‖ ^ 2)
      (fun x : E => inner ℝ x ((gaugeFixedBasePrecisionCLM K0 Q a) x))
      (fun i x => inner ℝ x (Sigma i x))
      M epsilon N I hbase
      (fun x => sq_nonneg ‖x‖)
      hM hepsilon hsmall hSigma x
  have hinner_sum :
      inner ℝ x (∑ i ∈ I, (Sigma i) x) =
        ∑ i ∈ I, inner ℝ x ((Sigma i) x) := by
    simp [inner_sum]
  simpa [IsCoerciveCLM, ContinuousLinearMap.sub_apply, inner_sub_right,
    ContinuousLinearMap.sum_apply] using
    hscalar.trans_eq (by rw [← hinner_sum])

/-- Strict pointwise positivity for finite block-Poincare defects controlled by
KP Catalan partial sums.  The physical/source identification of the selected
defects is deliberately left as the explicit `hSigma` hypothesis. -/
theorem inner_sub_finset_pos_of_catalanMajorantPartial_blockPoincare
    {ι E F : Type*}
    [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (K0 : E →L[ℝ] E)
    (Q : E →L[ℝ] F)
    (Sigma : ι → E →L[ℝ] E)
    (M epsilon : ι → ℝ)
    (N : ι → ℕ)
    (I : Finset ι)
    {a CP : ℝ}
    (ha : 0 ≤ a)
    (hCP : 0 < CP)
    (hK0nonneg :
      ∀ x : E, 0 ≤ inner ℝ x (K0 x))
    (hPoincare :
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          CP * (inner ℝ x (K0 x) + ‖Q x‖ ^ 2))
    (hM : ∀ i ∈ I, 0 < M i)
    (hepsilon : ∀ i ∈ I, 0 ≤ epsilon i)
    (hsmall : ∀ i ∈ I, 4 * M i ^ 2 * epsilon i ≤ 1)
    (hSigma :
      ∀ i, i ∈ I → ∀ x : E,
        inner ℝ x (Sigma i x) ≤
          YangMills.KP.catalanMajorantPartial (M i) (epsilon i) (N i) *
            ‖x‖ ^ 2)
    (hbudget :
      (∑ i ∈ I, schurCatalanBudget (M i) (epsilon i))
        < min 1 a / CP) :
    ∀ x : E, x ≠ 0 →
      0 <
        inner ℝ x
          ((gaugeFixedBasePrecisionCLM K0 Q a -
              ∑ i ∈ I, Sigma i) x) := by
  intro x hx
  have hbase :=
    isCoerciveCLM_gaugeFixedBasePrecision_of_blockPoincare
      K0 Q ha hCP hK0nonneg hPoincare
  have hxnorm : 0 < ‖x‖ ^ 2 := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx)
  have hscalar :=
    schurCatalan_coercive_of_catalanMajorantPartial_budget
      (fun x : E => ‖x‖ ^ 2)
      (fun x : E => inner ℝ x ((gaugeFixedBasePrecisionCLM K0 Q a) x))
      (fun i x => inner ℝ x (Sigma i x))
      M epsilon N I hbase
      (fun x => sq_nonneg ‖x‖)
      hM hepsilon hsmall hSigma hbudget x hxnorm
  have hinner_sum :
      inner ℝ x (∑ i ∈ I, (Sigma i) x) =
        ∑ i ∈ I, inner ℝ x ((Sigma i) x) := by
    simp [inner_sum]
  have hstrict :
      0 <
        inner ℝ x ((gaugeFixedBasePrecisionCLM K0 Q a) x) -
          inner ℝ x (∑ i ∈ I, (Sigma i) x) :=
    hscalar.trans_eq (by rw [← hinner_sum])
  have hlt :
      inner ℝ x (∑ i ∈ I, (Sigma i) x) <
        inner ℝ x ((gaugeFixedBasePrecisionCLM K0 Q a) x) :=
    sub_pos.mp hstrict
  simpa [ContinuousLinearMap.sub_apply, inner_sub_right,
    ContinuousLinearMap.sum_apply, sub_pos] using hlt

end YangMills.RG
