/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCanonicalInverseSqrt
import YangMills.RG.InverseSqrtResolventBochner

/-!
# Balakrishnan formula for the physical canonical inverse square root

The canonical physical root is now defined by the same Hermitian spectral
resolution consumed by the exact scalar integral.  Consequently the normalized
matrix Balakrishnan formula specializes literally to the CMP116 precision
matrix, without a separate uniqueness bridge.
-/

namespace YangMills.RG

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PhysicalGaugeCMP116Dictionary

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- Exact normalized Balakrishnan formula for the matrix underlying the
physical canonical inverse square root. -/
theorem inv_pi_smul_integral_physicalPrecisionMatrix
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    Real.pi⁻¹ •
        (∫ t in Ioi 0,
          (physicalPrecisionMatrix_posDef D K hc hcoer hK).isHermitian.cfc
            (inverseSqrtResolventSpectralKernel t)) =
      canonicalInverseSqrtMatrix D K hc hcoer hK := by
  exact
    inv_pi_smul_integral_isHermitianCfc_inverseSqrtResolventSpectralKernel
      (D.physicalRootMatrix K)
      (physicalPrecisionMatrix_posDef D K hc hcoer hK)

/-- The transported spectral kernel is exactly the scalar Balakrishnan
factor times the physical shifted resolvent. -/
theorem physicalCLMOfMatrix_cfc_inverseSqrtResolventSpectralKernel
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric)
    (t : ℝ) (ht : 0 ≤ t) :
    physicalCLMOfMatrix D
        ((physicalPrecisionMatrix_posDef
          D K hc hcoer hK).isHermitian.cfc
            (inverseSqrtResolventSpectralKernel t)) =
      (Real.sqrt t)⁻¹ •
        shiftedResolventOfIsCoerciveCLM K hc hcoer t ht := by
  let A := D.physicalRootMatrix K
  let M :=
    (physicalPrecisionMatrix_posDef
      D K hc hcoer hK).isHermitian.cfc
        (inverseSqrtResolventSpectralKernel t)
  have hshift :
      physicalCLMOfMatrix D
          (A + t • (1 :
            Matrix (CMP116CoordIndex d L lieDim)
              (CMP116CoordIndex d L lieDim) ℝ)) =
        shiftedPrecisionCLM K t := by
    rw [physicalCLMOfMatrix_add, physicalCLMOfMatrix_smul,
      physicalCLMOfMatrix_one,
      physicalCLMOfMatrix_physicalRootMatrix]
    rfl
  have hmat :
      M *
          (A + t • (1 :
            Matrix (CMP116CoordIndex d L lieDim)
              (CMP116CoordIndex d L lieDim) ℝ)) =
        (Real.sqrt t)⁻¹ •
          (1 : Matrix (CMP116CoordIndex d L lieDim)
            (CMP116CoordIndex d L lieDim) ℝ) := by
    exact
      isHermitianCfc_inverseSqrtResolventSpectralKernel_mul_shift
        A
        (physicalPrecisionMatrix_posDef D K hc hcoer hK)
        t ht
  have hop :
      (physicalCLMOfMatrix D M).comp (shiftedPrecisionCLM K t) =
        (Real.sqrt t)⁻¹ •
          ContinuousLinearMap.id ℝ
            (PhysicalGaugeOneCochain dPhys N Nc) := by
    rw [← hshift, ← physicalCLMOfMatrix_mul, hmat,
      physicalCLMOfMatrix_smul, physicalCLMOfMatrix_one]
  apply ContinuousLinearMap.ext
  intro x
  let R :=
    shiftedResolventOfIsCoerciveCLM K hc hcoer t ht
  calc
    physicalCLMOfMatrix D M x =
        physicalCLMOfMatrix D M
          (shiftedPrecisionCLM K t (R x)) := by
      rw [shiftedPrecisionCLM_apply_shiftedResolvent]
    _ = ((Real.sqrt t)⁻¹ •
          ContinuousLinearMap.id ℝ
            (PhysicalGaugeOneCochain dPhys N Nc)) (R x) := by
      exact congrArg (fun T => T (R x)) hop
    _ = ((Real.sqrt t)⁻¹ • R) x := by
      rfl

/-- Exact operator-level Balakrishnan formula for one physical canonical
inverse square root.  Unlike the difference formula below, the integrand has
one shifted resolvent and therefore one coercivity margin. -/
theorem physicalCanonicalInverseSqrt_eq_inv_pi_smul_integral_kernel
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c : ℝ} (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    physicalCanonicalInverseSqrt D K hc hcoer hK =
      Real.pi⁻¹ •
        (∫ t in Ioi 0,
          (Real.sqrt t)⁻¹ •
            nonnegativeShiftedResolvent K hc hcoer t) := by
  let hpos :=
    physicalPrecisionMatrix_posDef D K hc hcoer hK
  let F : ℝ → Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ :=
    fun t =>
      hpos.isHermitian.cfc
        (inverseSqrtResolventSpectralKernel t)
  have hFint :
      Integrable F (volume.restrict (Ioi 0)) :=
    integrableOn_isHermitianCfc_inverseSqrtResolventSpectralKernel
      (D.physicalRootMatrix K) hpos
  have hpoint (t : ℝ) (ht : 0 < t) :
      physicalCLMOfMatrixCLM D (F t) =
        (Real.sqrt t)⁻¹ •
          nonnegativeShiftedResolvent K hc hcoer t := by
    rw [physicalCLMOfMatrixCLM_apply]
    rw [nonnegativeShiftedResolvent_eq_of_nonneg K hc hcoer t ht.le]
    exact physicalCLMOfMatrix_cfc_inverseSqrtResolventSpectralKernel
      D K hc hcoer hK t ht.le
  symm
  calc
    Real.pi⁻¹ •
        (∫ t in Ioi 0,
          (Real.sqrt t)⁻¹ •
            nonnegativeShiftedResolvent K hc hcoer t) =
        Real.pi⁻¹ •
          (∫ t in Ioi 0, physicalCLMOfMatrixCLM D (F t)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hpoint t ht).symm
    _ =
        Real.pi⁻¹ •
          physicalCLMOfMatrixCLM D
            (∫ t in Ioi 0, F t) := by
      exact congrArg (fun T => Real.pi⁻¹ • T)
        ((physicalCLMOfMatrixCLM D).integral_comp_comm hFint)
    _ =
        physicalCLMOfMatrix D
          (Real.pi⁻¹ • (∫ t in Ioi 0, F t)) := by
      calc
        Real.pi⁻¹ •
            physicalCLMOfMatrixCLM D (∫ t in Ioi 0, F t) =
            physicalCLMOfMatrixCLM D
              (Real.pi⁻¹ • (∫ t in Ioi 0, F t)) :=
          ((physicalCLMOfMatrixCLM D).map_smul
            Real.pi⁻¹ (∫ t in Ioi 0, F t)).symm
        _ = physicalCLMOfMatrix D
              (Real.pi⁻¹ • (∫ t in Ioi 0, F t)) := rfl
    _ = physicalCanonicalInverseSqrt D K hc hcoer hK := by
      rw [inv_pi_smul_integral_physicalPrecisionMatrix
        D K hc hcoer hK]
      rfl

/-- Exact normalized Balakrishnan formula for the difference of two physical
canonical inverse square roots.  The integral is taken in the exact CMP116
matrix coordinates and then transported isometrically back to the physical
one-cochain space. -/
theorem physicalCLMOfMatrix_inv_pi_smul_integral_cfc_sub
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K₀ K₁ : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hcoer₀ : IsCoerciveCLM K₀ c₀)
    (hcoer₁ : IsCoerciveCLM K₁ c₁)
    (hK₀ : (K₀ : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric)
    (hK₁ : (K₁ : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    physicalCLMOfMatrix D
        (Real.pi⁻¹ •
          (∫ t in Ioi 0,
            (physicalPrecisionMatrix_posDef
                D K₁ hc₁ hcoer₁ hK₁).isHermitian.cfc
                (inverseSqrtResolventSpectralKernel t) -
              (physicalPrecisionMatrix_posDef
                D K₀ hc₀ hcoer₀ hK₀).isHermitian.cfc
                (inverseSqrtResolventSpectralKernel t))) =
      physicalCanonicalInverseSqrt D K₁ hc₁ hcoer₁ hK₁ -
        physicalCanonicalInverseSqrt D K₀ hc₀ hcoer₀ hK₀ := by
  rw [
    inv_pi_smul_integral_cfc_sub_eq_spectralInverseSqrtMatrix_sub
      (D.physicalRootMatrix K₀)
      (D.physicalRootMatrix K₁)
      (physicalPrecisionMatrix_posDef D K₀ hc₀ hcoer₀ hK₀)
      (physicalPrecisionMatrix_posDef D K₁ hc₁ hcoer₁ hK₁)]
  rw [physicalCLMOfMatrix_sub]
  rfl

/-- Exact operator-level Balakrishnan difference formula.  The central
resolvent defect is the already-factorized physical kernel, so no commutation
between the two precisions is used. -/
theorem physicalCanonicalInverseSqrt_sub_eq_inv_pi_smul_integral_kernel
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K₀ K₁ : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hcoer₀ : IsCoerciveCLM K₀ c₀)
    (hcoer₁ : IsCoerciveCLM K₁ c₁)
    (hK₀ : (K₀ : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric)
    (hK₁ : (K₁ : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    physicalCanonicalInverseSqrt D K₁ hc₁ hcoer₁ hK₁ -
        physicalCanonicalInverseSqrt D K₀ hc₀ hcoer₀ hK₀ =
      Real.pi⁻¹ •
        (∫ t in Ioi 0,
          inverseSqrtResolventDifferenceKernel
            K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ t) := by
  let hpos₀ :=
    physicalPrecisionMatrix_posDef D K₀ hc₀ hcoer₀ hK₀
  let hpos₁ :=
    physicalPrecisionMatrix_posDef D K₁ hc₁ hcoer₁ hK₁
  let F : ℝ → Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ :=
    fun t =>
      hpos₁.isHermitian.cfc
          (inverseSqrtResolventSpectralKernel t) -
        hpos₀.isHermitian.cfc
          (inverseSqrtResolventSpectralKernel t)
  have hFint :
      Integrable F (volume.restrict (Ioi 0)) := by
    exact
      (integrableOn_isHermitianCfc_inverseSqrtResolventSpectralKernel
        (D.physicalRootMatrix K₁) hpos₁).sub
        (integrableOn_isHermitianCfc_inverseSqrtResolventSpectralKernel
          (D.physicalRootMatrix K₀) hpos₀)
  have hpoint (t : ℝ) (ht : 0 < t) :
      physicalCLMOfMatrixCLM D (F t) =
        inverseSqrtResolventDifferenceKernel
          K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ t := by
    rw [physicalCLMOfMatrixCLM_apply]
    dsimp only [F]
    rw [physicalCLMOfMatrix_sub]
    rw [
      physicalCLMOfMatrix_cfc_inverseSqrtResolventSpectralKernel
        D K₁ hc₁ hcoer₁ hK₁ t ht.le,
      physicalCLMOfMatrix_cfc_inverseSqrtResolventSpectralKernel
        D K₀ hc₀ hcoer₀ hK₀ t ht.le]
    rw [inverseSqrtResolventDifferenceKernel,
      nonnegativeShiftedResolvent_eq_of_nonneg
        K₁ hc₁ hcoer₁ t ht.le,
      nonnegativeShiftedResolvent_eq_of_nonneg
        K₀ hc₀ hcoer₀ t ht.le]
    exact (smul_sub (Real.sqrt t)⁻¹ _ _).symm
  symm
  calc
    Real.pi⁻¹ •
        (∫ t in Ioi 0,
          inverseSqrtResolventDifferenceKernel
            K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ t) =
        Real.pi⁻¹ •
          (∫ t in Ioi 0, physicalCLMOfMatrixCLM D (F t)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hpoint t ht).symm
    _ =
        Real.pi⁻¹ •
          physicalCLMOfMatrixCLM D
            (∫ t in Ioi 0, F t) := by
      exact congrArg (fun T => Real.pi⁻¹ • T)
        ((physicalCLMOfMatrixCLM D).integral_comp_comm hFint)
    _ =
        physicalCLMOfMatrix D
          (Real.pi⁻¹ • (∫ t in Ioi 0, F t)) := by
      calc
        Real.pi⁻¹ •
            physicalCLMOfMatrixCLM D (∫ t in Ioi 0, F t) =
            physicalCLMOfMatrixCLM D
              (Real.pi⁻¹ • (∫ t in Ioi 0, F t)) :=
          ((physicalCLMOfMatrixCLM D).map_smul
            Real.pi⁻¹ (∫ t in Ioi 0, F t)).symm
        _ = physicalCLMOfMatrix D
              (Real.pi⁻¹ • (∫ t in Ioi 0, F t)) := rfl
    _ =
        physicalCanonicalInverseSqrt D K₁ hc₁ hcoer₁ hK₁ -
          physicalCanonicalInverseSqrt D K₀ hc₀ hcoer₀ hK₀ := by
      exact physicalCLMOfMatrix_inv_pi_smul_integral_cfc_sub
        D K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ hK₀ hK₁

/-- Norm comparison reduced to the exact scalar two-margin integral. -/
theorem norm_physicalCanonicalInverseSqrt_sub_le_scalarIntegral
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (K₀ K₁ : PhysicalGaugeOneCochain dPhys N Nc →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hcoer₀ : IsCoerciveCLM K₀ c₀)
    (hcoer₁ : IsCoerciveCLM K₁ c₁)
    (hK₀ : (K₀ : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric)
    (hK₁ : (K₁ : PhysicalGaugeOneCochain dPhys N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc).IsSymmetric) :
    ‖physicalCanonicalInverseSqrt D K₁ hc₁ hcoer₁ hK₁ -
        physicalCanonicalInverseSqrt D K₀ hc₀ hcoer₀ hK₀‖ ≤
      Real.pi⁻¹ *
        (‖K₀ - K₁‖ *
          (∫ t in Ioi 0,
            inverseSqrtTwoMarginScalar c₀ c₁ t)) := by
  rw [physicalCanonicalInverseSqrt_sub_eq_inv_pi_smul_integral_kernel
    D K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ hK₀ hK₁]
  rw [norm_smul]
  have hpiNorm : ‖(Real.pi⁻¹ : ℝ)‖ = Real.pi⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr Real.pi_pos)]
  rw [hpiNorm]
  apply mul_le_mul_of_nonneg_left
  · calc
      ‖∫ t in Ioi 0,
          inverseSqrtResolventDifferenceKernel
            K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ t‖ ≤
          ∫ t in Ioi 0,
            ‖K₀ - K₁‖ *
              inverseSqrtTwoMarginScalar c₀ c₁ t := by
        apply norm_integral_le_of_norm_le
          ((integrableOn_inverseSqrtTwoMarginScalar hc₀ hc₁).const_mul
            ‖K₀ - K₁‖)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact norm_inverseSqrtResolventDifferenceKernel_le_twoMargin
          K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ t ht.le
      _ = ‖K₀ - K₁‖ *
          (∫ t in Ioi 0,
            inverseSqrtTwoMarginScalar c₀ c₁ t) := by
        rw [integral_const_mul]
  · exact (inv_pos.mpr Real.pi_pos).le

end PhysicalGaugeCMP116Dictionary

end

end YangMills.RG
