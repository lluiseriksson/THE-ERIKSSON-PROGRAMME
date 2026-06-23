/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.GaugeFixedCovariance
import YangMills.RG.PhysicalGaugeFlatPoincare

/-!
# Fixed-volume flat physical gauge-fixed precision and covariance

This module is the first physical-cochain adapter after the full-periodic flat
Hodge/block Poincare theorem.  It specializes the source-independent
`K0 + a Q†Q - Σ` coercivity API to the flat physical Hodge operator and the
flat block constraint on finite periodic positive-bond one-cochains, and then
specializes the exact finite-dimensional covariance construction to the same
operator.

The result is intentionally fixed-volume.  It does not assert a
volume-uniform Poincare constant, identify the flat Hodge operator with a
Wilson Hessian, localize the inverse covariance or its square root, or
construct `hraw`.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

/-- The flat physical gauge-fixed precision shell
`K0 + a Q†Q - Σ` on finite periodic positive-bond one-cochains.

Here `K0` is the trivial-background flat Hodge operator and `Q` is the flat
block constraint.  This is still pre-Wilson-Hessian bookkeeping: all physical
identification and uniformity claims remain external obligations. -/
noncomputable def flatGaugeFixedPrecisionCLM
    {ι : Type*}
    (d L N' Nc : ℕ) [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (a : ℝ)
    (Sigma :
      ι →
        FinePhysicalOneCochain d L N' Nc →L[ℝ]
          FinePhysicalOneCochain d L N' Nc) :
    FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  gaugeFixedPrecisionCLM
    (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
    (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')
    a Sigma

/-- Fixed-volume flat Poincare plus a strict summable perturbation budget gives
coercivity of the flat physical gauge-fixed precision shell.

The constant `CP` is supplied explicitly, so the theorem does not hide any
uniformity or source-estimate obligation. -/
theorem flatGaugeFixedPrecision_coerciveWithPositiveConstant_of_flatPoincare
    {ι : Type*}
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Sigma :
      ι →
        FinePhysicalOneCochain d L N' Nc →L[ℝ]
          FinePhysicalOneCochain d L N' Nc)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP)
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    0 < (min 1 a / CP - ∑' i, δ i) ∧
    IsCoerciveCLM
      (flatGaugeFixedPrecisionCLM d L N' Nc ρ a Sigma)
      (min 1 a / CP - ∑' i, δ i) := by
  simpa [flatGaugeFixedPrecisionCLM] using
    gaugeFixedPrecision_coerciveWithPositiveConstant
      (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
      (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')
      Sigma δ ha hP.1
      (fun A =>
        flatGaugeHodgeK0_nonnegative_right
          (d := d) (N := L * N') (Nc := Nc) ρ A)
      hP.2 hδ hSigmaδ hbudget

/-- Unconditional fixed-volume adapter: the proved finite periodic flat
Hodge/block Poincare theorem supplies some `CP`, and the caller keeps the
small-budget obligation explicit for whichever `CP` is selected.

This is still qualitative and fixed-volume. -/
theorem exists_flatGaugeFixedPrecision_coerciveWithPositiveConstant
    {ι : Type*}
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Sigma :
      ι →
        FinePhysicalOneCochain d L N' Nc →L[ℝ]
          FinePhysicalOneCochain d L N' Nc)
    (δ : ι → ℝ)
    {a : ℝ}
    (ha : 0 < a)
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      ∀ CP : ℝ,
        FlatGaugeHodgePoincare d L N' Nc ρ CP →
          (∑' i, δ i) < min 1 a / CP) :
    ∃ CP : ℝ,
      0 < (min 1 a / CP - ∑' i, δ i) ∧
      IsCoerciveCLM
        (flatGaugeFixedPrecisionCLM d L N' Nc ρ a Sigma)
        (min 1 a / CP - ∑' i, δ i) := by
  obtain ⟨CP, hP⟩ :=
    exists_flatGaugeHodgePoincare
      (d := d) (L := L) (N' := N') (Nc := Nc) ρ
  exact
    ⟨CP,
      flatGaugeFixedPrecision_coerciveWithPositiveConstant_of_flatPoincare
        ρ Sigma δ ha hP hδ hSigmaδ (hbudget CP hP)⟩

/-- The exact finite-dimensional covariance of the fixed-volume flat physical
gauge-fixed precision shell.

This packages the inverse of `flatGaugeFixedPrecisionCLM` under the same
fixed-volume Poincare and strict perturbation-budget hypotheses as the
coercivity theorem.  It does not assert localization or identify the operator
with a Wilson Hessian. -/
noncomputable def flatGaugeFixedCovarianceCLM
    {ι : Type*}
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Sigma :
      ι →
        FinePhysicalOneCochain d L N' Nc →L[ℝ]
          FinePhysicalOneCochain d L N' Nc)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP)
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  covarianceOfGaugeFixedPrecisionCLM
    (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
    (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')
    Sigma δ ha hP.1
    (fun A =>
      flatGaugeHodgeK0_nonnegative_right
        (d := d) (N := L * N') (Nc := Nc) ρ A)
    hP.2 hδ hSigmaδ hbudget

/-- The flat physical covariance is a left inverse of the flat physical
gauge-fixed precision. -/
theorem flatGaugeFixedCovarianceCLM_comp_precision
    {ι : Type*}
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Sigma :
      ι →
        FinePhysicalOneCochain d L N' Nc →L[ℝ]
          FinePhysicalOneCochain d L N' Nc)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP)
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    (flatGaugeFixedCovarianceCLM
        ρ Sigma δ ha hP hδ hSigmaδ hbudget).comp
      (flatGaugeFixedPrecisionCLM d L N' Nc ρ a Sigma) =
        ContinuousLinearMap.id ℝ (FinePhysicalOneCochain d L N' Nc) := by
  simpa [flatGaugeFixedCovarianceCLM, flatGaugeFixedPrecisionCLM] using
    covarianceOfGaugeFixedPrecisionCLM_comp_precision
      (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
      (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')
      Sigma δ ha hP.1
      (fun A =>
        flatGaugeHodgeK0_nonnegative_right
          (d := d) (N := L * N') (Nc := Nc) ρ A)
      hP.2 hδ hSigmaδ hbudget

/-- The flat physical covariance is a right inverse of the flat physical
gauge-fixed precision. -/
theorem precision_comp_flatGaugeFixedCovarianceCLM
    {ι : Type*}
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Sigma :
      ι →
        FinePhysicalOneCochain d L N' Nc →L[ℝ]
          FinePhysicalOneCochain d L N' Nc)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP)
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    (flatGaugeFixedPrecisionCLM d L N' Nc ρ a Sigma).comp
      (flatGaugeFixedCovarianceCLM
        ρ Sigma δ ha hP hδ hSigmaδ hbudget) =
        ContinuousLinearMap.id ℝ (FinePhysicalOneCochain d L N' Nc) := by
  simpa [flatGaugeFixedCovarianceCLM, flatGaugeFixedPrecisionCLM] using
    precision_comp_covarianceOfGaugeFixedPrecisionCLM
      (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
      (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')
      Sigma δ ha hP.1
      (fun A =>
        flatGaugeHodgeK0_nonnegative_right
          (d := d) (N := L * N') (Nc := Nc) ρ A)
      hP.2 hδ hSigmaδ hbudget

/-- Operator-norm bound for the fixed-volume flat physical covariance. -/
theorem norm_flatGaugeFixedCovarianceCLM_le
    {ι : Type*}
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Sigma :
      ι →
        FinePhysicalOneCochain d L N' Nc →L[ℝ]
          FinePhysicalOneCochain d L N' Nc)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP)
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP) :
    ‖flatGaugeFixedCovarianceCLM
        ρ Sigma δ ha hP hδ hSigmaδ hbudget‖ ≤
      (gaugeFixedResidualCoercivityConstant δ a CP)⁻¹ := by
  change
    ‖covarianceOfGaugeFixedPrecisionCLM
        (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')
        Sigma δ ha hP.1
        (fun A =>
          flatGaugeHodgeK0_nonnegative_right
            (d := d) (N := L * N') (Nc := Nc) ρ A)
        hP.2 hδ hSigmaδ hbudget‖ ≤
      (gaugeFixedResidualCoercivityConstant δ a CP)⁻¹
  exact
    norm_covarianceOfGaugeFixedPrecisionCLM_le
      (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
      (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')
      Sigma δ ha hP.1
      (fun A =>
        flatGaugeHodgeK0_nonnegative_right
          (d := d) (N := L * N') (Nc := Nc) ρ A)
      hP.2 hδ hSigmaδ hbudget

/-- Positive-semidefinite quadratic form for the fixed-volume flat physical
covariance. -/
theorem flatGaugeFixedCovarianceCLM_psd
    {ι : Type*}
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Sigma :
      ι →
        FinePhysicalOneCochain d L N' Nc →L[ℝ]
          FinePhysicalOneCochain d L N' Nc)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP)
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP)
    (y : FinePhysicalOneCochain d L N' Nc) :
    0 ≤
      inner ℝ y
        (flatGaugeFixedCovarianceCLM
          ρ Sigma δ ha hP hδ hSigmaδ hbudget y) := by
  simpa [flatGaugeFixedCovarianceCLM] using
    covarianceOfGaugeFixedPrecisionCLM_psd
      (flatGaugeHodgeK0CLM d (L * N') Nc ρ)
      (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N')
      Sigma δ ha hP.1
      (fun A =>
        flatGaugeHodgeK0_nonnegative_right
          (d := d) (N := L * N') (Nc := Nc) ρ A)
      hP.2 hδ hSigmaδ hbudget y

end YangMills.RG
