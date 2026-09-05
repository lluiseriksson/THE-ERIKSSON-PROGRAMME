/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalSourceBackgroundLipschitz
import YangMills.RG.BalabanCMP102PhysicalRightVariationBound
import YangMills.RG.NoncommutativePowerLipschitz

/-!
# Background Lipschitz control of the CMP98 logarithmic first variation

This module propagates the literal source-contour estimates through the
Mercator derivative and the normalized block average.  If

`m = 2(d+1)M`,

then the pointwise telescope

`D log(D_U) H_U - D log(D_0) H_0`

costs

`(B₂(r) + B₁(r)) m² ε ‖A‖∞`.

The factor `M⁻ᵈ` in the physical block average cancels `|blockOf| = Mᵈ`
exactly, so no volume cardinality remains.

The tangent `A` remains arbitrary.  This estimate concerns the CMP109 pivot
operator and must not be specialized using the CMP116 Gaussian cutoff.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp102PhysicalLogAverageBackgroundMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Explicit background-Lipschitz budget for the value of the normalized
logarithmic average. -/
def cmp102PhysicalLogAverageBackgroundValueBudget
    (d M : ℕ) (r ε : ℝ) : ℝ :=
  nearLogDerivativeBudget r *
    ((2 * (d + 1) * M : ℕ) : ℝ) * ε

/-- Explicit background-Lipschitz budget for the normalized logarithmic first
variation. -/
def cmp102PhysicalLogAverageBackgroundDerivativeBudget
    (d M : ℕ) (r ε : ℝ) : ℝ :=
  (nearLogSecondDerivativeBudget r + nearLogDerivativeBudget r) *
    ((2 * (d + 1) * M : ℕ) : ℝ) ^ 2 * ε

theorem cmp102PhysicalLogAverageBackgroundValueBudget_nonneg
    {d M : ℕ} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) :
    0 ≤ cmp102PhysicalLogAverageBackgroundValueBudget d M r ε := by
  unfold cmp102PhysicalLogAverageBackgroundValueBudget
  exact mul_nonneg
    (mul_nonneg (nearLogDerivativeBudget_nonneg r hr) (by positivity))
    hε

theorem cmp102PhysicalLogAverageBackgroundDerivativeBudget_nonneg
    {d M : ℕ} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) :
    0 ≤ cmp102PhysicalLogAverageBackgroundDerivativeBudget d M r ε := by
  unfold cmp102PhysicalLogAverageBackgroundDerivativeBudget
  exact mul_nonneg
    (mul_nonneg
      (add_nonneg
        (nearLogSecondDerivativeBudget_nonneg r hr)
        (nearLogDerivativeBudget_nonneg r hr))
      (sq_nonneg _))
    hε

/-- The normalized logarithmic average itself is background-Lipschitz with
the literal source-contour length and no periodic-volume loss. -/
theorem norm_cmp98UbarLogAverage_zero_sub_trivial_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε r : ℝ) (hε : 0 ≤ ε) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (b : PhysicalBond d N')
    (hbaseU : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ r)
    (hbase0 : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix
        (trivialPhysicalGaugeBackground d (M * N') Nc) b x 0‖ ≤ r) :
    ‖cmp98UbarLogAverage U b 0 -
        cmp98UbarLogAverage
          (trivialPhysicalGaugeBackground d (M * N') Nc) b 0‖ ≤
      cmp102PhysicalLogAverageBackgroundValueBudget d M r ε := by
  let U0 := trivialPhysicalGaugeBackground d (M * N') Nc
  let m : ℝ := ((2 * (d + 1) * M : ℕ) : ℝ)
  let DU : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x => cmp98UbarAmbientDeviationMatrix U b x 0
  let D0 : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x => cmp98UbarAmbientDeviationMatrix U0 b x 0
  let localU : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x => nearLog (DU x)
  let local0 : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x => nearLog (D0 x)
  let C := cmp102PhysicalLogAverageBackgroundValueBudget d M r ε
  have hpoint :
      ∀ x ∈ blockOf M N' b.1, ‖localU x - local0 x‖ ≤ C := by
    intro x hx
    have hDU : ‖DU x‖ ≤ r := hbaseU x hx
    have hD0 : ‖D0 x‖ ≤ r := by
      simpa only [D0, U0] using hbase0 x hx
    have hDUdiff : ‖DU x - D0 x‖ ≤ m * ε := by
      simpa only [DU, D0, U0, m] using
        norm_cmp98UbarAmbientDeviationMatrix_zero_sub_trivial_le_sourceScale
          U ε hε hsmall
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b x hx
    calc
      ‖localU x - local0 x‖
          ≤ nearLogDerivativeBudget r * ‖DU x - D0 x‖ :=
        norm_nearLog_sub_nearLog_le hr0 hr1 hDU hD0
      _ ≤ nearLogDerivativeBudget r * (m * ε) :=
        mul_le_mul_of_nonneg_left hDUdiff
          (nearLogDerivativeBudget_nonneg r hr0)
      _ = C := by
        unfold C cmp102PhysicalLogAverageBackgroundValueBudget m
        ring
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hMd : (M : ℝ) ^ d ≠ 0 := pow_ne_zero d hM
  unfold cmp98UbarLogAverage
  change
    ‖((M : ℝ) ^ d)⁻¹ •
          (∑ x ∈ blockOf M N' b.1, localU x) -
        ((M : ℝ) ^ d)⁻¹ •
          (∑ x ∈ blockOf M N' b.1, local0 x)‖ ≤ _
  have hsumDiff :
      (∑ x ∈ blockOf M N' b.1, localU x) -
          ∑ x ∈ blockOf M N' b.1, local0 x =
        ∑ x ∈ blockOf M N' b.1, (localU x - local0 x) := by
    exact (Finset.sum_sub_distrib localU local0).symm
  have havgReal :
      ((M : ℝ) ^ d)⁻¹ •
            (∑ x ∈ blockOf M N' b.1, localU x) -
          ((M : ℝ) ^ d)⁻¹ •
            (∑ x ∈ blockOf M N' b.1, local0 x) =
        ((M : ℝ) ^ d)⁻¹ •
          (∑ x ∈ blockOf M N' b.1, (localU x - local0 x)) := by
    calc
      ((M : ℝ) ^ d)⁻¹ •
            (∑ x ∈ blockOf M N' b.1, localU x) -
          ((M : ℝ) ^ d)⁻¹ •
            (∑ x ∈ blockOf M N' b.1, local0 x) =
        ((M : ℝ) ^ d)⁻¹ •
          ((∑ x ∈ blockOf M N' b.1, localU x) -
            ∑ x ∈ blockOf M N' b.1, local0 x) :=
        (smul_sub _ _ _).symm
      _ = _ := congrArg _ hsumDiff
  rw [havgReal]
  have hrealComplex :
      ((M : ℝ) ^ d)⁻¹ •
          (∑ x ∈ blockOf M N' b.1, (localU x - local0 x)) =
        (((M : ℝ) ^ d)⁻¹ : ℂ) •
          (∑ x ∈ blockOf M N' b.1, (localU x - local0 x)) := by
    ext i j
    simp [RCLike.real_smul_eq_coe_mul]
  rw [hrealComplex, norm_smul]
  have hnormc : ‖(((M : ℝ) ^ d)⁻¹ : ℂ)‖ = ((M : ℝ) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg M)]
  rw [hnormc]
  calc
    ((M : ℝ) ^ d)⁻¹ *
        ‖∑ x ∈ blockOf M N' b.1, (localU x - local0 x)‖
        ≤ ((M : ℝ) ^ d)⁻¹ *
            ∑ x ∈ blockOf M N' b.1, ‖localU x - local0 x‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ ((M : ℝ) ^ d)⁻¹ *
          ∑ _x ∈ blockOf M N' b.1, C := by
      gcongr with x hx
      exact hpoint x hx
    _ = C := by
      rw [Finset.sum_const, blockOf_card]
      simp only [nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_assoc, inv_mul_cancel₀ hMd, one_mul]
    _ = cmp102PhysicalLogAverageBackgroundValueBudget d M r ε := rfl

/-- The physical logarithmic first variation is background-Lipschitz with an
explicit source-scale constant and no periodic-volume loss. -/
theorem norm_cmp98UbarLogAveragePhysicalVariation_sub_trivial_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε r : ℝ) (hε : 0 ≤ ε) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hbaseU : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ r)
    (hbase0 : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix
        (trivialPhysicalGaugeBackground d (M * N') Nc) b x 0‖ ≤ r) :
    ‖cmp98UbarLogAveragePhysicalVariation U A b -
        cmp98UbarLogAveragePhysicalVariation
          (trivialPhysicalGaugeBackground d (M * N') Nc) A b‖ ≤
      cmp102PhysicalLogAverageBackgroundDerivativeBudget d M r ε *
        cmp98SourceFieldSupNorm A := by
  let U0 := trivialPhysicalGaugeBackground d (M * N') Nc
  let m : ℝ := ((2 * (d + 1) * M : ℕ) : ℝ)
  let S : ℝ := cmp98SourceFieldSupNorm A
  let DU : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x => cmp98UbarAmbientDeviationMatrix U b x 0
  let D0 : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x => cmp98UbarAmbientDeviationMatrix U0 b x 0
  let HU : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x => cmp98UbarDeviationFirstVariation U A b x 0
  let H0 : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x => cmp98UbarDeviationFirstVariation U0 A b x 0
  let localU : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x =>
      (fderiv ℝ
        (nearLog : Matrix (Fin Nc) (Fin Nc) ℂ →
          Matrix (Fin Nc) (Fin Nc) ℂ) (DU x)) (HU x)
  let local0 : FinBox d (M * N') → Matrix (Fin Nc) (Fin Nc) ℂ :=
    fun x =>
      (fderiv ℝ
        (nearLog : Matrix (Fin Nc) (Fin Nc) ℂ →
          Matrix (Fin Nc) (Fin Nc) ℂ) (D0 x)) (H0 x)
  let C :=
    cmp102PhysicalLogAverageBackgroundDerivativeBudget d M r ε * S
  have hm0 : 0 ≤ m := by
    dsimp only [m]
    positivity
  have hS0 : 0 ≤ S := by
    exact cmp98SourceFieldSupNorm_nonneg A
  have hpoint :
      ∀ x ∈ blockOf M N' b.1, ‖localU x - local0 x‖ ≤ C := by
    intro x hx
    have hDU : ‖DU x‖ ≤ r := hbaseU x hx
    have hD0 : ‖D0 x‖ ≤ r := by
      simpa only [D0, U0] using hbase0 x hx
    have hDUdiff : ‖DU x - D0 x‖ ≤ m * ε := by
      simpa only [DU, D0, U0, m] using
        norm_cmp98UbarAmbientDeviationMatrix_zero_sub_trivial_le_sourceScale
          U ε hε hsmall A b x hx
    have hHU : ‖HU x‖ ≤ m * S := by
      simpa only [HU, m, S] using
        norm_cmp98UbarDeviationFirstVariation_zero_le_sourceScale
          U A b x hx
    have hHdiff : ‖HU x - H0 x‖ ≤ m ^ 2 * ε * S := by
      simpa only [HU, H0, U0, m, S] using
        norm_cmp98UbarDeviationFirstVariation_zero_sub_trivial_le_sourceScale
          U ε hε hsmall A b x hx
    let AZ := fderiv ℝ
      (nearLog : Matrix (Fin Nc) (Fin Nc) ℂ →
        Matrix (Fin Nc) (Fin Nc) ℂ) (DU x)
    let AW := fderiv ℝ
      (nearLog : Matrix (Fin Nc) (Fin Nc) ℂ →
        Matrix (Fin Nc) (Fin Nc) ℂ) (D0 x)
    have hAZAW :
        ‖AZ - AW‖ ≤
          nearLogSecondDerivativeBudget r * (m * ε) := by
      exact
        (norm_fderiv_nearLog_sub_le_secondDerivativeBudget
          hr0 hr1 hDU hD0).trans
          (mul_le_mul_of_nonneg_left hDUdiff
            (nearLogSecondDerivativeBudget_nonneg r hr0))
    have hAW : ‖AW‖ ≤ nearLogDerivativeBudget r := by
      exact norm_fderiv_nearLog_le_derivativeBudget hr0 hr1 hD0
    have halg :
        localU x - local0 x =
          (AZ - AW) (HU x) + AW (HU x - H0 x) := by
      change AZ (HU x) - AW (H0 x) =
        (AZ (HU x) - AW (HU x)) + AW (HU x - H0 x)
      rw [AW.map_sub]
      abel
    calc
      ‖localU x - local0 x‖ =
          ‖(AZ - AW) (HU x) + AW (HU x - H0 x)‖ :=
        congrArg norm halg
      _
          ≤ ‖(AZ - AW) (HU x)‖ +
              ‖AW (HU x - H0 x)‖ := norm_add_le _ _
      _ ≤ (nearLogSecondDerivativeBudget r * (m * ε)) * (m * S) +
            nearLogDerivativeBudget r * (m ^ 2 * ε * S) := by
        apply add_le_add
        · exact ((AZ - AW).le_opNorm (HU x)).trans
            (mul_le_mul hAZAW hHU (norm_nonneg _)
              ((norm_nonneg _).trans hAZAW))
        · exact (AW.le_opNorm (HU x - H0 x)).trans
            (mul_le_mul hAW hHdiff (norm_nonneg _)
              ((norm_nonneg _).trans hAW))
      _ = C := by
        unfold C cmp102PhysicalLogAverageBackgroundDerivativeBudget m S
        ring
  have hsumU :
      (∑ x ∈ blockOf M N' b.1,
          (∑' n : ℕ, nearLogTermFDeriv (DU x) n) (HU x)) =
        ∑ x ∈ blockOf M N' b.1, localU x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hlt : ‖DU x‖ < 1 := (hbaseU x hx).trans_lt hr1
    have hfd :
        fderiv ℝ
            (nearLog : Matrix (Fin Nc) (Fin Nc) ℂ →
              Matrix (Fin Nc) (Fin Nc) ℂ) (DU x) =
          ∑' n : ℕ, nearLogTermFDeriv (DU x) n :=
      (hasFDerivAt_nearLog_of_norm_lt_one hlt).fderiv
    rw [← hfd]
    rfl
  have hsum0 :
      (∑ x ∈ blockOf M N' b.1,
          (∑' n : ℕ, nearLogTermFDeriv (D0 x) n) (H0 x)) =
        ∑ x ∈ blockOf M N' b.1, local0 x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hlt : ‖D0 x‖ < 1 := (hbase0 x hx).trans_lt hr1
    have hfd :
        fderiv ℝ
            (nearLog : Matrix (Fin Nc) (Fin Nc) ℂ →
              Matrix (Fin Nc) (Fin Nc) ℂ) (D0 x) =
          ∑' n : ℕ, nearLogTermFDeriv (D0 x) n :=
      (hasFDerivAt_nearLog_of_norm_lt_one hlt).fderiv
    rw [← hfd]
    rfl
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hMd : (M : ℝ) ^ d ≠ 0 := pow_ne_zero d hM
  unfold cmp98UbarLogAveragePhysicalVariation
  change
    ‖((M : ℝ) ^ d)⁻¹ •
          (∑ x ∈ blockOf M N' b.1,
            (∑' n : ℕ, nearLogTermFDeriv (DU x) n) (HU x)) -
        ((M : ℝ) ^ d)⁻¹ •
          (∑ x ∈ blockOf M N' b.1,
            (∑' n : ℕ, nearLogTermFDeriv (D0 x) n) (H0 x))‖ ≤ _
  rw [hsumU, hsum0]
  have hsumDiff :
      (∑ x ∈ blockOf M N' b.1, localU x) -
          ∑ x ∈ blockOf M N' b.1, local0 x =
        ∑ x ∈ blockOf M N' b.1, (localU x - local0 x) := by
    exact (Finset.sum_sub_distrib localU local0).symm
  have havgReal :
      ((M : ℝ) ^ d)⁻¹ •
            (∑ x ∈ blockOf M N' b.1, localU x) -
          ((M : ℝ) ^ d)⁻¹ •
            (∑ x ∈ blockOf M N' b.1, local0 x) =
        ((M : ℝ) ^ d)⁻¹ •
          (∑ x ∈ blockOf M N' b.1, (localU x - local0 x)) := by
    calc
      ((M : ℝ) ^ d)⁻¹ •
            (∑ x ∈ blockOf M N' b.1, localU x) -
          ((M : ℝ) ^ d)⁻¹ •
            (∑ x ∈ blockOf M N' b.1, local0 x) =
        ((M : ℝ) ^ d)⁻¹ •
          ((∑ x ∈ blockOf M N' b.1, localU x) -
            ∑ x ∈ blockOf M N' b.1, local0 x) :=
        (smul_sub _ _ _).symm
      _ = _ := congrArg _ hsumDiff
  rw [havgReal]
  have hrealComplex :
      ((M : ℝ) ^ d)⁻¹ •
          (∑ x ∈ blockOf M N' b.1, (localU x - local0 x)) =
        (((M : ℝ) ^ d)⁻¹ : ℂ) •
          (∑ x ∈ blockOf M N' b.1, (localU x - local0 x)) := by
    ext i j
    simp [RCLike.real_smul_eq_coe_mul]
  rw [hrealComplex, norm_smul]
  have hnormc : ‖(((M : ℝ) ^ d)⁻¹ : ℂ)‖ = ((M : ℝ) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg M)]
  rw [hnormc]
  calc
    ((M : ℝ) ^ d)⁻¹ *
        ‖∑ x ∈ blockOf M N' b.1, (localU x - local0 x)‖
        ≤ ((M : ℝ) ^ d)⁻¹ *
            ∑ x ∈ blockOf M N' b.1, ‖localU x - local0 x‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ ((M : ℝ) ^ d)⁻¹ *
          ∑ _x ∈ blockOf M N' b.1, C := by
      gcongr with x hx
      exact hpoint x hx
    _ = C := by
      rw [Finset.sum_const, blockOf_card]
      simp only [nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_assoc, inv_mul_cancel₀ hMd, one_mul]
    _ = cmp102PhysicalLogAverageBackgroundDerivativeBudget d M r ε *
          cmp98SourceFieldSupNorm A := rfl

end

end YangMills.RG
