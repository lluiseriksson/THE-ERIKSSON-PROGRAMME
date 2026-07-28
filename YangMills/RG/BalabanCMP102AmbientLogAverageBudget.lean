/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientLocalNearLogBudget

/-!
# Exact normalized-block budgets for the CMP98 logarithmic average

The literal CMP98 exponent is `M⁻ᵈ` times a sum over exactly `Mᵈ` fine
sites.  This module proves the cancellation once and consumes the pointwise
Mercator estimates for values and Fréchet derivatives.  No factor depending
on the block size or the periodic volume survives.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102AmbientLogAverageMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

local instance cmp102AmbientLogAverageCLMNorm :
    Norm (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
      Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousLinearMap.hasOpNorm

local instance cmp102AmbientLogAverageCLMSeminormedAddCommGroup :
    SeminormedAddCommGroup
      (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
      Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance cmp102AmbientLogAverageCLMNormedSpace :
    NormedSpace ℝ
      (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ) :=
  ContinuousLinearMap.toNormedSpace

/-- Exact cancellation of the normalized cardinality of one physical block. -/
theorem norm_normalized_block_sum_le
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (b : FinBox d N')
    (f : FinBox d (M * N') → E) {C : ℝ}
    (hpoint : ∀ x ∈ blockOf M N' b, ‖f x‖ ≤ C) :
    ‖((M : ℝ) ^ d)⁻¹ • ∑ x ∈ blockOf M N' b, f x‖ ≤ C := by
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hMd : (M : ℝ) ^ d ≠ 0 := pow_ne_zero d hM
  have hMd0 : 0 ≤ (M : ℝ) ^ d := pow_nonneg (Nat.cast_nonneg M) d
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hMd0)]
  calc
    ((M : ℝ) ^ d)⁻¹ * ‖∑ x ∈ blockOf M N' b, f x‖
        ≤ ((M : ℝ) ^ d)⁻¹ *
            ∑ x ∈ blockOf M N' b, ‖f x‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ ((M : ℝ) ^ d)⁻¹ *
          ∑ _x ∈ blockOf M N' b, C := by
      gcongr with x hx
      exact hpoint x hx
    _ = C := by
      rw [Finset.sum_const, blockOf_card]
      simp only [nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_assoc, inv_mul_cancel₀ hMd, one_mul]

/-- The normalized logarithmic block average inherits the pointwise source
value budget with no cardinality loss. -/
theorem norm_cmp98UbarLogAverage_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q) :
    ‖cmp98UbarLogAverage U b Z‖ ≤
      cmp102SourceLocalNearLogValueBudget q := by
  unfold cmp98UbarLogAverage
  apply norm_normalized_block_sum_le b.1
  intro x hx
  exact norm_nearLog_cmp98UbarAmbientDeviationMatrix_le_sourceBudget
    U b x Z hq0 hq1 (hD x hx)

/-- The derivative of the normalized logarithmic block average inherits the
pointwise derivative budget with no cardinality loss. -/
theorem norm_fderiv_cmp98UbarLogAverage_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hZ : ‖Z‖ ≤ r)
    (hD : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q) :
    ‖fderiv ℝ (cmp98UbarLogAverage U b) Z‖ ≤
      cmp102SourceLocalNearLogDerivativeBudget d M r q := by
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1 :=
    fun x hx => (hD x hx).trans_lt hq1
  let L :
      PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    ((M : ℝ) ^ d)⁻¹ •
      ∑ x ∈ blockOf M N' b.1,
        ((∑' n : ℕ,
            nearLogTermFDeriv
              (cmp98UbarAmbientDeviationMatrix U b x Z) n).comp
          (fderiv ℝ
            (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z))
  have hfd : fderiv ℝ (cmp98UbarLogAverage U b) Z = L := by
    simpa only [L] using
      (hasFDerivAt_cmp98UbarLogAverage U b Z hsmall).fderiv
  calc
    ‖fderiv ℝ (cmp98UbarLogAverage U b) Z‖ = ‖L‖ :=
      congrArg norm hfd
    _ ≤ cmp102SourceLocalNearLogDerivativeBudget d M r q := by
      unfold L
      apply norm_normalized_block_sum_le
        (M := M) (N' := N')
        (E := PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
          Matrix (Fin Nc) (Fin Nc) ℂ) b.1
      intro x hx
      have hlocal :=
        ((HasFDerivAt.nearLog_of_norm_lt_one
          (analyticAt_cmp98UbarAmbientDeviationMatrix U b x Z
            ).differentiableAt.hasFDerivAt
          (hsmall x hx))).fderiv
      have hpoint :=
        norm_fderiv_nearLog_cmp98UbarAmbientDeviationMatrix_le_sourceBudget
          U b x hx Z hr hq0 hq1 hZ (hD x hx)
      change ContinuousLinearMap.opNorm
        (fderiv ℝ
          (fun W : PhysicalAmbientMatrixTangent d (M * N') Nc => nearLog
            (cmp98UbarAmbientDeviationMatrix U b x W)) Z) ≤ _ at hpoint
      change ContinuousLinearMap.opNorm
        ((∑' n : ℕ,
            nearLogTermFDeriv
              (cmp98UbarAmbientDeviationMatrix U b x Z) n).comp
          (fderiv ℝ
            (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z)) ≤ _
      calc
        ContinuousLinearMap.opNorm
            ((∑' n : ℕ,
                nearLogTermFDeriv
                  (cmp98UbarAmbientDeviationMatrix U b x Z) n).comp
              (fderiv ℝ
                (fun W => cmp98UbarAmbientDeviationMatrix U b x W) Z)) =
            ContinuousLinearMap.opNorm
              (fderiv ℝ
                (fun W => nearLog
                  (cmp98UbarAmbientDeviationMatrix U b x W)) Z) :=
          congrArg ContinuousLinearMap.opNorm hlocal.symm
        _ ≤ cmp102SourceLocalNearLogDerivativeBudget d M r q := hpoint

/-- The normalized logarithmic block average inherits the pointwise
two-field Lipschitz budget with no cardinality loss. -/
theorem norm_cmp98UbarLogAverage_sub_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r)
    (hDZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q)
    (hDW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ ≤ q) :
    ‖cmp98UbarLogAverage U b Z - cmp98UbarLogAverage U b W‖ ≤
      cmp102SourceLocalNearLogValueLipschitzBudget d M r q *
        ‖Z - W‖ := by
  rw [cmp98UbarLogAverage, cmp98UbarLogAverage]
  have hsmul :
      ((M : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf M N' b.1,
            nearLog (cmp98UbarAmbientDeviationMatrix U b x Z) -
        ((M : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf M N' b.1,
            nearLog (cmp98UbarAmbientDeviationMatrix U b x W) =
      ((M : ℝ) ^ d)⁻¹ •
        ((∑ x ∈ blockOf M N' b.1,
            nearLog (cmp98UbarAmbientDeviationMatrix U b x Z)) -
          ∑ x ∈ blockOf M N' b.1,
            nearLog (cmp98UbarAmbientDeviationMatrix U b x W)) := by
    module
  have hsum :
      (∑ x ∈ blockOf M N' b.1,
          nearLog (cmp98UbarAmbientDeviationMatrix U b x Z)) -
        ∑ x ∈ blockOf M N' b.1,
          nearLog (cmp98UbarAmbientDeviationMatrix U b x W) =
      ∑ x ∈ blockOf M N' b.1,
        (nearLog (cmp98UbarAmbientDeviationMatrix U b x Z) -
          nearLog (cmp98UbarAmbientDeviationMatrix U b x W)) := by
    exact (Finset.sum_sub_distrib
      (fun x => nearLog (cmp98UbarAmbientDeviationMatrix U b x Z))
      (fun x => nearLog (cmp98UbarAmbientDeviationMatrix U b x W))).symm
  rw [hsmul, hsum]
  apply norm_normalized_block_sum_le b.1
  intro x hx
  exact
    norm_nearLog_cmp98UbarAmbientDeviationMatrix_sub_le_sourceBudget
      U b x hx Z W hr hq0 hq1 hZ hW (hDZ x hx) (hDW x hx)

/-- The derivative of the normalized logarithmic block average inherits the
pointwise derivative-Lipschitz budget with no cardinality loss. -/
theorem norm_fderiv_cmp98UbarLogAverage_sub_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r)
    (hDZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q)
    (hDW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ ≤ q) :
    ‖fderiv ℝ (cmp98UbarLogAverage U b) Z -
        fderiv ℝ (cmp98UbarLogAverage U b) W‖ ≤
      cmp102SourceLocalNearLogDerivativeLipschitzBudget d M r q *
        ‖Z - W‖ := by
  have hsmallZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1 :=
    fun x hx => (hDZ x hx).trans_lt hq1
  have hsmallW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ < 1 :=
    fun x hx => (hDW x hx).trans_lt hq1
  let LZ :
      PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    ((M : ℝ) ^ d)⁻¹ •
      ∑ x ∈ blockOf M N' b.1,
        ((∑' n : ℕ,
            nearLogTermFDeriv
              (cmp98UbarAmbientDeviationMatrix U b x Z) n).comp
          (fderiv ℝ
            (fun V => cmp98UbarAmbientDeviationMatrix U b x V) Z))
  let LW :
      PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
        Matrix (Fin Nc) (Fin Nc) ℂ :=
    ((M : ℝ) ^ d)⁻¹ •
      ∑ x ∈ blockOf M N' b.1,
        ((∑' n : ℕ,
            nearLogTermFDeriv
              (cmp98UbarAmbientDeviationMatrix U b x W) n).comp
          (fderiv ℝ
            (fun V => cmp98UbarAmbientDeviationMatrix U b x V) W))
  have hfdZ : fderiv ℝ (cmp98UbarLogAverage U b) Z = LZ := by
    simpa only [LZ] using
      (hasFDerivAt_cmp98UbarLogAverage U b Z hsmallZ).fderiv
  have hfdW : fderiv ℝ (cmp98UbarLogAverage U b) W = LW := by
    simpa only [LW] using
      (hasFDerivAt_cmp98UbarLogAverage U b W hsmallW).fderiv
  let FZ :
      FinBox d (M * N') →
        (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
          Matrix (Fin Nc) (Fin Nc) ℂ) :=
    fun x =>
      ((∑' n : ℕ,
          nearLogTermFDeriv
            (cmp98UbarAmbientDeviationMatrix U b x Z) n).comp
        (fderiv ℝ
          (fun V => cmp98UbarAmbientDeviationMatrix U b x V) Z))
  let FW :
      FinBox d (M * N') →
        (PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
          Matrix (Fin Nc) (Fin Nc) ℂ) :=
    fun x =>
      ((∑' n : ℕ,
          nearLogTermFDeriv
            (cmp98UbarAmbientDeviationMatrix U b x W) n).comp
        (fderiv ℝ
          (fun V => cmp98UbarAmbientDeviationMatrix U b x V) W))
  have hrewrite :
      LZ - LW =
      ((M : ℝ) ^ d)⁻¹ •
        ∑ x ∈ blockOf M N' b.1, (FZ x - FW x) := by
    have hsmul :
        ((M : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf M N' b.1,
            FZ x -
          ((M : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf M N' b.1,
            FW x =
        ((M : ℝ) ^ d)⁻¹ •
          ((∑ x ∈ blockOf M N' b.1, FZ x) -
            ∑ x ∈ blockOf M N' b.1, FW x) := by
      module
    have hsum :
        (∑ x ∈ blockOf M N' b.1, FZ x) -
          ∑ x ∈ blockOf M N' b.1, FW x =
        ∑ x ∈ blockOf M N' b.1, (FZ x - FW x) := by
      exact (Finset.sum_sub_distrib FZ FW).symm
    change
      ((M : ℝ) ^ d)⁻¹ • ∑ x ∈ blockOf M N' b.1, FZ x -
          ((M : ℝ) ^ d)⁻¹ • ∑ x ∈ blockOf M N' b.1, FW x =
        ((M : ℝ) ^ d)⁻¹ • ∑ x ∈ blockOf M N' b.1, (FZ x - FW x)
    rw [hsmul, hsum]
  calc
    ‖fderiv ℝ (cmp98UbarLogAverage U b) Z -
        fderiv ℝ (cmp98UbarLogAverage U b) W‖ =
        ‖LZ - LW‖ := congrArg norm (congrArg₂ (· - ·) hfdZ hfdW)
    _ = ‖((M : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf M N' b.1, (FZ x - FW x)‖ :=
      congrArg norm hrewrite
    _ ≤ cmp102SourceLocalNearLogDerivativeLipschitzBudget d M r q *
          ‖Z - W‖ := by
      apply norm_normalized_block_sum_le
        (M := M) (N' := N')
        (E := PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
          Matrix (Fin Nc) (Fin Nc) ℂ) b.1
      intro x hx
      have hlocalZ :=
        ((HasFDerivAt.nearLog_of_norm_lt_one
          (analyticAt_cmp98UbarAmbientDeviationMatrix U b x Z
            ).differentiableAt.hasFDerivAt
          (hsmallZ x hx))).fderiv
      have hlocalW :=
        ((HasFDerivAt.nearLog_of_norm_lt_one
          (analyticAt_cmp98UbarAmbientDeviationMatrix U b x W
            ).differentiableAt.hasFDerivAt
          (hsmallW x hx))).fderiv
      have hpoint :=
        norm_fderiv_nearLog_cmp98UbarAmbientDeviationMatrix_sub_le_sourceBudget
          U b x hx Z W hr hq0 hq1 hZ hW (hDZ x hx) (hDW x hx)
      change ContinuousLinearMap.opNorm
        (fderiv ℝ
            (fun V : PhysicalAmbientMatrixTangent d (M * N') Nc => nearLog
              (cmp98UbarAmbientDeviationMatrix U b x V)) Z -
          fderiv ℝ
            (fun V : PhysicalAmbientMatrixTangent d (M * N') Nc => nearLog
              (cmp98UbarAmbientDeviationMatrix U b x V)) W) ≤ _ at hpoint
      change ContinuousLinearMap.opNorm (FZ x - FW x) ≤ _
      calc
        ContinuousLinearMap.opNorm (FZ x - FW x) =
            ContinuousLinearMap.opNorm
              (fderiv ℝ
                  (fun V => nearLog
                    (cmp98UbarAmbientDeviationMatrix U b x V)) Z -
                fderiv ℝ
                  (fun V => nearLog
                    (cmp98UbarAmbientDeviationMatrix U b x V)) W) := by
          apply congrArg ContinuousLinearMap.opNorm
          exact congrArg₂ (· - ·) hlocalZ.symm hlocalW.symm
        _ ≤ cmp102SourceLocalNearLogDerivativeLipschitzBudget d M r q *
              ‖Z - W‖ := hpoint

end

end YangMills.RG
