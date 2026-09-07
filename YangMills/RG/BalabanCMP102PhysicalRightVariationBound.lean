/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalFirstVariationBound

/-!
# Source-sup-norm bound for the physical CMP98 right variation

This module completes the linear estimate left visible by the two-field
CMP102 correction theorem.  The local contour derivative is passed through
the normalized Mercator average, `g(ad)`, and the transported coarse
variation.  Every constant is generated from the source radii and literal
path lengths; no right-variation bound is supplied by the caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102RightVariationBoundMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The normalized logarithmic average first variation inherits the literal
four-contour source-length bound, with exact cancellation of the block
cardinality. -/
theorem norm_cmp98UbarLogAveragePhysicalVariation_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hr13 : 1 / 3 ≤ r) (hr1 : r < 1) :
    ‖cmp98UbarLogAveragePhysicalVariation U A b‖ ≤
      nearLogDerivativeBudget r *
        (((2 * (d + 1) * M : ℕ) : ℝ) *
          cmp98SourceFieldSupNorm A) := by
  let C := nearLogDerivativeBudget r *
    (((2 * (d + 1) * M : ℕ) : ℝ) * cmp98SourceFieldSupNorm A)
  let Dp : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x => cmp98UbarDeviationFirstVariation U A b x 0
  let localTerm : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x =>
      (∑' n : ℕ,
        nearLogTermFDeriv
          (cmp98UbarAmbientDeviationMatrix U b x 0) n) (Dp x)
  let S : Matrix (Fin Nc) (Fin Nc) ℂ :=
    ∑ x ∈ blockOf M N' b.1, localTerm x
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13
  have hpoint : ∀ x ∈ blockOf M N' b.1, ‖localTerm x‖ ≤ C := by
    intro x hx
    let D0 := cmp98UbarAmbientDeviationMatrix U b x 0
    let L := fderiv ℝ
      (nearLog : Matrix (Fin Nc) (Fin Nc) ℂ →
        Matrix (Fin Nc) (Fin Nc) ℂ) D0
    have hD0 : ‖D0‖ ≤ r := (hbase x hx).trans hr13
    have hlt : ‖D0‖ < 1 := hD0.trans_lt hr1
    have hfd :
        L = ∑' n : ℕ, nearLogTermFDeriv D0 n := by
      exact (hasFDerivAt_nearLog_of_norm_lt_one hlt).fderiv
    have hL : ‖L‖ ≤ nearLogDerivativeBudget r := by
      exact norm_fderiv_nearLog_le_derivativeBudget hr0 hr1 hD0
    have hDp : ‖Dp x‖ ≤
        ((2 * (d + 1) * M : ℕ) : ℝ) *
          cmp98SourceFieldSupNorm A := by
      exact norm_cmp98UbarDeviationFirstVariation_zero_le_sourceScale
        U A b x hx
    change ‖(∑' n : ℕ, nearLogTermFDeriv D0 n) (Dp x)‖ ≤ C
    rw [← hfd]
    exact (L.le_opNorm (Dp x)).trans
      (mul_le_mul hL hDp (norm_nonneg _)
        ((norm_nonneg _).trans hL))
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hMd : (M : ℝ) ^ d ≠ 0 := pow_ne_zero d hM
  unfold cmp98UbarLogAveragePhysicalVariation
  change ‖((M : ℝ) ^ d)⁻¹ • S‖ ≤ _
  have hrealComplex :
      ((M : ℝ) ^ d)⁻¹ • S = (((M : ℝ) ^ d)⁻¹ : ℂ) • S := by
    ext i j
    simp [RCLike.real_smul_eq_coe_mul]
  rw [hrealComplex, norm_smul]
  have hnormc : ‖(((M : ℝ) ^ d)⁻¹ : ℂ)‖ = ((M : ℝ) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg M)]
  rw [hnormc]
  calc
    ((M : ℝ) ^ d)⁻¹ * ‖S‖
        ≤ ((M : ℝ) ^ d)⁻¹ *
            ∑ x ∈ blockOf M N' b.1, ‖localTerm x‖ := by
          gcongr
          dsimp only [S]
          exact norm_sum_le _ _
    _ ≤ ((M : ℝ) ^ d)⁻¹ *
          ∑ _x ∈ blockOf M N' b.1, C := by
      gcongr with x hx
      exact hpoint x hx
    _ = C := by
      rw [Finset.sum_const, blockOf_card]
      simp only [nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_assoc, inv_mul_cancel₀ hMd, one_mul]
    _ = nearLogDerivativeBudget r *
        (((2 * (d + 1) * M : ℕ) : ℝ) *
          cmp98SourceFieldSupNorm A) := rfl

set_option maxHeartbeats 1000000 in
/-- Generic Banach-algebra form of the `g(ad Y)` action bound. -/
theorem norm_cmp98GAd_apply_le_exp_two_mul_of_normedRing
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (Y H : 𝔸) (R : ℝ) (hY : ‖Y‖ ≤ R) :
    ‖cmp98GAd Y H‖ ≤ Real.exp (2 * R) * ‖H‖ := by
  have htail := norm_cmp98GAd_sub_id_le_exp_sub_one Y
  let T : 𝔸 →L[ℝ] 𝔸 :=
    cmp98GAd Y - ContinuousLinearMap.id ℝ 𝔸
  have htailT : ‖T‖ ≤ Real.exp (2 * ‖Y‖) - 1 := by
    simpa [T] using htail
  have hdecomp :
      cmp98GAd Y H = T H + H := by
    simp [T]
  rw [hdecomp]
  calc
    ‖T H + H‖
        ≤ ‖T H‖ + ‖H‖ :=
      norm_add_le _ _
    _ ≤ ‖T‖ * ‖H‖ + ‖H‖ := by
      gcongr
      exact T.le_opNorm H
    _ ≤ (Real.exp (2 * ‖Y‖) - 1) * ‖H‖ + ‖H‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right htailT (norm_nonneg H))
        (le_refl ‖H‖)
    _ = Real.exp (2 * ‖Y‖) * ‖H‖ := by ring
    _ ≤ Real.exp (2 * R) * ‖H‖ := by
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hY (by norm_num)))
        (norm_nonneg H)

/-- `g(ad Y)` acts with norm at most `exp(2R)` on a matrix radius-`R` ball. -/
theorem norm_cmp98GAd_apply_le_exp_two_mul
    (Y H : Matrix (Fin Nc) (Fin Nc) ℂ) (R : ℝ)
    (hY : ‖Y‖ ≤ R) :
    ‖cmp98GAd Y H‖ ≤ Real.exp (2 * R) * ‖H‖ :=
  norm_cmp98GAd_apply_le_exp_two_mul_of_normedRing Y H R hY

/-- Explicit coefficient multiplying the source field sup norm in the
physical right-variation estimate. -/
def cmp102SourceRightVariationLinearRate
    (d M : ℕ) (r : ℝ) : ℝ :=
  let R := cmp98SourceLogAverageRadius r
  Real.exp (2 * R) * nearLogDerivativeBudget r *
      ((2 * (d + 1) * M : ℕ) : ℝ) +
    cmp98SourceOuterExpNormBudget r ^ 2 * (M : ℝ)

/-- The literal physical right variation is bounded by the source field sup
norm, uniformly in the periodic volume. -/
theorem norm_cmp98Eq119NonlinearRightVariation_le_sourceSupNorm
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hr13 : 1 / 3 ≤ r) (hr1 : r < 1) :
    ‖cmp98Eq119NonlinearRightVariation U A b‖ ≤
      cmp102SourceRightVariationLinearRate d M r *
        cmp98SourceFieldSupNorm A := by
  let R := cmp98SourceLogAverageRadius r
  let Y := cmp98UbarLogAverage U b 0
  let H := cmp98UbarLogAveragePhysicalVariation U A b
  let K := cmp98Eq119CoarseRightVariation U A b
  let O := cmp98SourceOuterExpNormBudget r
  let S := cmp98SourceFieldSupNorm A
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13
  have hR0 : 0 ≤ R := cmp98SourceLogAverageRadius_nonneg r hr0
  have hYbase : ‖Y‖ ≤ nearLogDerivativeBudget r * (1 / 3 : ℝ) := by
    simpa [Y] using norm_cmp98UbarLogAverage_zero_le
      U b r hbase hr13 hr1
  have hY : ‖Y‖ ≤ R := by
    have hB := nearLogDerivativeBudget_nonneg r hr0
    exact hYbase.trans (by
      dsimp only [R, cmp98SourceLogAverageRadius]
      exact mul_le_mul_of_nonneg_left hr13 hB)
  have hH : ‖H‖ ≤ nearLogDerivativeBudget r *
      (((2 * (d + 1) * M : ℕ) : ℝ) * S) := by
    simpa [H, S] using
      norm_cmp98UbarLogAveragePhysicalVariation_le_sourceScale
        U A b r hbase hr13 hr1
  have hK : ‖K‖ ≤ (M : ℝ) * S := by
    simpa [K, S] using
      norm_cmp98Eq119CoarseRightVariation_le_sourceScale U A b
  have hExpY : ‖NormedSpace.exp Y‖ ≤ O := by
    simpa [Y, O, cmp98UbarExpAverage] using
      norm_cmp98UbarExpAverage_zero_le_sourceBudget
        U b r hbase hr13 hr1
  have hExpNegY : ‖NormedSpace.exp (-Y)‖ ≤ O := by
    have hneg : ‖-Y‖ ≤ R := by simpa using hY
    have hraw := norm_exp_le_derivativeBudgets hR0 hneg
    simpa [O, cmp98SourceOuterExpNormBudget, R] using hraw
  have hgad : ‖cmp98GAd (-Y) H‖ ≤
      Real.exp (2 * R) *
        (nearLogDerivativeBudget r *
          (((2 * (d + 1) * M : ℕ) : ℝ) * S)) := by
    exact (norm_cmp98GAd_apply_le_exp_two_mul (-Y) H R
      (by simpa using hY)).trans
        (mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le)
  have hdirect :
      ‖NormedSpace.exp Y * K * NormedSpace.exp (-Y)‖ ≤
        O ^ 2 * ((M : ℝ) * S) := by
    calc
      ‖NormedSpace.exp Y * K * NormedSpace.exp (-Y)‖
          ≤ (‖NormedSpace.exp Y‖ * ‖K‖) *
              ‖NormedSpace.exp (-Y)‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
            (norm_nonneg _))
      _ ≤ (O * ((M : ℝ) * S)) * O := by
        exact mul_le_mul
          (mul_le_mul hExpY hK (norm_nonneg _)
            ((norm_nonneg _).trans hExpY))
          hExpNegY (norm_nonneg _)
          (mul_nonneg
            ((norm_nonneg _).trans hExpY)
            ((norm_nonneg _).trans hK))
      _ = O ^ 2 * ((M : ℝ) * S) := by ring
  have hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
    intro x hx
    exact (hbase x hx).trans_lt (by norm_num)
  rw [cmp98Eq119NonlinearRightVariation_eq U A b hsmall]
  change ‖cmp98GAd (-Y) H +
    NormedSpace.exp Y * K * NormedSpace.exp (-Y)‖ ≤ _
  unfold cmp102SourceRightVariationLinearRate
  dsimp only
  calc
    ‖cmp98GAd (-Y) H +
        NormedSpace.exp Y * K * NormedSpace.exp (-Y)‖
        ≤ ‖cmp98GAd (-Y) H‖ +
            ‖NormedSpace.exp Y * K * NormedSpace.exp (-Y)‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (2 * R) *
          (nearLogDerivativeBudget r *
            (((2 * (d + 1) * M : ℕ) : ℝ) * S)) +
        O ^ 2 * ((M : ℝ) * S) :=
      add_le_add hgad hdirect
    _ = (Real.exp (2 * R) * nearLogDerivativeBudget r *
          ((2 * (d + 1) * M : ℕ) : ℝ) +
        O ^ 2 * (M : ℝ)) * S := by ring

end

end YangMills.RG
