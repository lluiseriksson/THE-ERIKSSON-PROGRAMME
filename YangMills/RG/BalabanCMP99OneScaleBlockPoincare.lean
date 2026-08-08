/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99CovariantPathControl
import YangMills.RG.BalabanCMP99FiniteMeanControl
import YangMills.RG.BalabanCMP99SourceWeightedRegionalAdjoint
import YangMills.RG.BalabanCMP99SourceAdjointTransport

/-!
# One-scale physical block Poincare estimate for the CMP99 source average

This file composes the literal block contours, their localized covariant
energy and the source coefficient `M^{-d}`.  The result is an explicit
one-scale Poincare estimate whose constant depends on `M,d` but not on the
ambient periodic volume `N'`.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The literal source-normalized adjoint average on one full physical block. -/
noncomputable def cmp99FullSourceBlockAverageValue
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') : SUNLieCoord Nc :=
  cmp99SourceBlockAverageWeight M d •
    ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
      rho.adCLM
        (cmp99ContourHolonomy
          (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1)
        (phi x.1)

/-- The full-periodic one-scale source average as a zero-cochain. -/
noncomputable def cmp99FullSourceBlockAverage
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc) :
    PhysicalGaugeZeroCochain d (M * N') Nc →L[ℝ]
      PhysicalGaugeZeroCochain d N' Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := fun phi => WithLp.toLp 2 fun y =>
        cmp99FullSourceBlockAverageValue rho U phi y
      map_add' := fun phi psi => by
        apply PiLp.ext
        intro y
        simp only [cmp99FullSourceBlockAverageValue, PiLp.add_apply,
          map_add, Finset.sum_add_distrib, smul_add]
      map_smul' := fun a phi => by
        apply PiLp.ext
        intro y
        simp only [cmp99FullSourceBlockAverageValue, PiLp.smul_apply,
          map_smul, Finset.smul_sum, smul_smul, RingHom.id_apply]
        rw [mul_comm (cmp99SourceBlockAverageWeight M d) a] }

@[simp] theorem cmp99FullSourceBlockAverage_apply
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') :
    cmp99FullSourceBlockAverage rho U phi y =
      cmp99FullSourceBlockAverageValue rho U phi y := rfl

/-- One-block estimate.  The derivative contribution is localized to the
same block and the constant-mode contribution is the literal source average. -/
theorem sum_norm_sq_block_le_covariantEnergy_add_average
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc)
    (y : FinBox d N') :
    (∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
      ‖phi x.1‖ ^ 2) ≤
      6 * (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
        cmp99BlockCovariantEnergy rho U phi y) +
      3 * (M : ℝ) ^ d *
        ‖cmp99FullSourceBlockAverageValue rho U phi y‖ ^ 2 := by
  let I := {x : FinBox d (M * N') // x ∈ blockOf M N' y}
  let base : SUNLieCoord Nc := phi (blockBasepoint M N' y)
  let v : I → SUNLieCoord Nc := fun x =>
    rho.adCLM
      (cmp99ContourHolonomy
        (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1)
      (phi x.1)
  have hw : 0 ≤ cmp99SourceBlockAverageWeight M d := by
    unfold cmp99SourceBlockAverageWeight
    positivity
  have hnorm : cmp99SourceBlockAverageWeight M d *
      (Fintype.card I : ℝ) = 1 := by
    change cmp99SourceBlockAverageWeight M d *
      (Fintype.card {x : FinBox d (M * N') // x ∈ blockOf M N' y} : ℝ) = 1
    rw [Fintype.card_coe, blockOf_card, Nat.cast_pow]
    exact cmp99SourceBlockAverageWeight_mul_card (M := M) (d := d)
  have hmean :=
    sum_norm_sq_le_six_sum_base_defect_sq_add_three_card_mean_sq
      (I := I) (E := SUNLieCoord Nc)
      (cmp99SourceBlockAverageWeight M d) hw hnorm base v
  have hleft : (∑ x : I, ‖phi x.1‖ ^ 2) =
      ∑ x : I, ‖v x‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _hx
    simp only [v]
    rw [rho.norm_ad]
  have hdefect : (∑ x : I, ‖base - v x‖ ^ 2) ≤
      (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
        cmp99BlockCovariantEnergy rho U phi y) := by
    simpa only [I, base, v] using
      sum_norm_cmp99BlockContainedContour_defect_sq_le rho U phi y
  have hcard : (Fintype.card I : ℝ) = (M : ℝ) ^ d := by
    change (Fintype.card
      {x : FinBox d (M * N') // x ∈ blockOf M N' y} : ℝ) = _
    rw [Fintype.card_coe, blockOf_card]
    norm_cast
  have hmeanValue :
      cmp99SourceBlockAverageWeight M d • (∑ x : I, v x) =
        cmp99FullSourceBlockAverageValue rho U phi y := rfl
  rw [hleft]
  calc
    ∑ x : I, ‖v x‖ ^ 2 ≤
        6 * (∑ x : I, ‖base - v x‖ ^ 2) +
          3 * (Fintype.card I : ℝ) *
            ‖cmp99SourceBlockAverageWeight M d • (∑ x : I, v x)‖ ^ 2 :=
      hmean
    _ ≤ 6 * ((M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
          cmp99BlockCovariantEnergy rho U phi y)) +
        3 * (M : ℝ) ^ d *
          ‖cmp99FullSourceBlockAverageValue rho U phi y‖ ^ 2 := by
      rw [hcard, hmeanValue]
      gcongr
    _ = 6 * (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2 *
          cmp99BlockCovariantEnergy rho U phi y) +
        3 * (M : ℝ) ^ d *
          ‖cmp99FullSourceBlockAverageValue rho U phi y‖ ^ 2 := by ring

/-- The explicit one-scale source Poincare constant. -/
noncomputable def cmp99OneScaleBlockPoincareConstant (d M : ℕ) : ℝ :=
  max
    (6 * (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2))
    (3 * (M : ℝ) ^ d)

theorem cmp99OneScaleBlockPoincareConstant_pos :
    0 < cmp99OneScaleBlockPoincareConstant d M := by
  unfold cmp99OneScaleBlockPoincareConstant
  have hM : 0 < (M : ℝ) := by exact_mod_cast NeZero.pos M
  have hright : 0 < 3 * (M : ℝ) ^ d := by positivity
  exact lt_of_lt_of_le hright (le_max_right _ _)

/-- Uniform full-periodic one-scale Poincare estimate for the literal CMP99
source average.  No constant depends on `N'`. -/
theorem norm_sq_le_cmp99OneScaleBlockPoincare
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : PhysicalGaugeZeroCochain d (M * N') Nc) :
    ‖phi‖ ^ 2 ≤
      cmp99OneScaleBlockPoincareConstant d M *
        (‖covariantD0CLM rho U phi‖ ^ 2 +
          ‖cmp99FullSourceBlockAverage rho U phi‖ ^ 2) := by
  let A : ℝ :=
    6 * (M : ℝ) ^ d * (((d * (M - 1) : ℕ) : ℝ) ^ 2)
  let B : ℝ := 3 * (M : ℝ) ^ d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hblocks :
      ‖phi‖ ^ 2 =
        ∑ y : FinBox d N',
          ∑ x ∈ blockOf M N' y, ‖phi x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact (sum_blockOf M N' (fun x => ‖phi x‖ ^ 2)).symm
  have hsum :
      ‖phi‖ ^ 2 ≤
        A * ‖covariantD0CLM rho U phi‖ ^ 2 +
          B * ‖cmp99FullSourceBlockAverage rho U phi‖ ^ 2 := by
    rw [hblocks]
    calc
      ∑ y : FinBox d N', ∑ x ∈ blockOf M N' y, ‖phi x‖ ^ 2 =
          ∑ y : FinBox d N',
            ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
              ‖phi x.1‖ ^ 2 := by
                apply Finset.sum_congr rfl
                intro y _hy
                exact Finset.sum_subtype (blockOf M N' y)
                  (fun x => Iff.rfl) (fun x => ‖phi x‖ ^ 2)
      _ ≤ ∑ y : FinBox d N',
          (A * cmp99BlockCovariantEnergy rho U phi y +
            B * ‖cmp99FullSourceBlockAverageValue rho U phi y‖ ^ 2) := by
              apply Finset.sum_le_sum
              intro y _hy
              simpa only [A, B, mul_assoc] using
                sum_norm_sq_block_le_covariantEnergy_add_average
                  rho U phi y
      _ = A * ‖covariantD0CLM rho U phi‖ ^ 2 +
          B * ‖cmp99FullSourceBlockAverage rho U phi‖ ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum,
              sum_cmp99BlockCovariantEnergy_eq_norm_sq,
              ← Finset.mul_sum]
            rw [PiLp.norm_sq_eq_of_L2 _
              (cmp99FullSourceBlockAverage rho U phi)]
            rfl
  calc
    ‖phi‖ ^ 2 ≤ A * ‖covariantD0CLM rho U phi‖ ^ 2 +
        B * ‖cmp99FullSourceBlockAverage rho U phi‖ ^ 2 := hsum
    _ ≤ max A B *
        (‖covariantD0CLM rho U phi‖ ^ 2 +
          ‖cmp99FullSourceBlockAverage rho U phi‖ ^ 2) := by
      have hAle : A ≤ max A B := le_max_left _ _
      have hBle : B ≤ max A B := le_max_right _ _
      nlinarith [sq_nonneg ‖covariantD0CLM rho U phi‖,
        sq_nonneg ‖cmp99FullSourceBlockAverage rho U phi‖]
    _ = cmp99OneScaleBlockPoincareConstant d M *
        (‖covariantD0CLM rho U phi‖ ^ 2 +
          ‖cmp99FullSourceBlockAverage rho U phi‖ ^ 2) := by rfl

end

end YangMills.RG
