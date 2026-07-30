/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109PhysicalPivotNoMixing
import YangMills.RG.BalabanCMP109PhysicalConstraintRightInverse
import YangMills.RG.BalabanCMP98Eq124Eq125RightNormalization

/-!
# Flat calibration of the physical CMP109 pivot response

The physical pivot response is already known to be pointwise in the coarse
bond.  This file calibrates its matching coefficient at the trivial
background.  It keeps the complete represented CMP98 block until the literal
entrance, middle, exit, and coarse-contour contributions have been evaluated;
it does not identify the complete CMP98 operator with the shorter main term
of equation (125) by definition.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 2000000

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]

/-- At the trivial background and zero ambient tangent, every literal
physical Wilson line is the identity matrix. -/
@[simp] theorem cmp98AmbientWilsonLineMatrix_trivial_zero
    (es : List (ConcreteEdge d (L * N'))) :
    cmp98AmbientWilsonLineMatrix
        (trivialPhysicalGaugeBackground d (L * N') Nc) 0 es = 1 := by
  rw [cmp98AmbientWilsonLineMatrix_zero_eq_wilsonLine]
  have hline :
      wilsonLine (trivialPhysicalGaugeBackground d (L * N') Nc) es = 1 := by
    apply wilsonLine_one
    intro e
    rfl
  exact congrArg Subtype.val hline

/-- The physical contour curve has the same trivial-background value. -/
@[simp] theorem cmp98ContourMatrixCurve_trivial_zero
    (A : FinePhysicalOneCochain d L N' Nc)
    (es : List (ConcreteEdge d (L * N'))) :
    cmp98ContourMatrixCurve
        (trivialPhysicalGaugeBackground d (L * N') Nc) A es 0 = 1 := by
  rw [cmp98ContourMatrixCurve_zero_eq_wilsonLine]
  have hline :
      wilsonLine (trivialPhysicalGaugeBackground d (L * N') Nc) es = 1 := by
    apply wilsonLine_one
    intro e
    rfl
  exact congrArg Subtype.val hline

/-- The four-contour deviation vanishes exactly at the trivial background
and zero ambient tangent. -/
@[simp] theorem cmp98UbarAmbientDeviationMatrix_trivial_zero
    (b : PhysicalBond d N') (x : FinBox d (L * N')) :
    cmp98UbarAmbientDeviationMatrix
        (trivialPhysicalGaugeBackground d (L * N') Nc) b x 0 = 0 := by
  unfold cmp98UbarAmbientDeviationMatrix
  simp

/-- The averaged logarithmic coordinate is exactly zero at the trivial
background. -/
@[simp] theorem cmp98UbarLogAverage_trivial_zero
    (b : PhysicalBond d N') :
    cmp98UbarLogAverage
        (trivialPhysicalGaugeBackground d (L * N') Nc) b 0 = 0 := by
  unfold cmp98UbarLogAverage
  simp only [cmp98UbarAmbientDeviationMatrix_trivial_zero, nearLog_zero,
    Finset.sum_const_zero]
  exact smul_zero _

/-- The literal right-normalizing inverse of the represented block is the
identity at the trivial background. -/
@[simp] theorem cmp98Eq119NonlinearBlockInverseAtZero_trivial
    (A : FinePhysicalOneCochain d L N' Nc)
    (b : PhysicalBond d N') :
    cmp98Eq119NonlinearBlockInverseAtZero
        (trivialPhysicalGaugeBackground d (L * N') Nc) A b = 1 := by
  unfold cmp98Eq119NonlinearBlockInverseAtZero
  rw [cmp98ContourMatrixCurve_zero_eq_wilsonLine,
    cmp98UbarLogAverage_trivial_zero]
  have hline :
      wilsonLine (trivialPhysicalGaugeBackground d (L * N') Nc)
          (cmp98SourceCoarseBondPath (Nc := Nc) (M := L) b) = 1 := by
    apply wilsonLine_one
    intro e
    rfl
  rw [hline]
  simp

/-- The Neumann-defined inverse of `g(ad Y)` is the identity at `Y=0`. -/
@[simp] theorem cmp98GAdInv_zero_apply
    (H : Matrix (Fin Nc) (Fin Nc) ℂ) :
    cmp98GAdInv (0 : Matrix (Fin Nc) (Fin Nc) ℂ) H = H := by
  unfold cmp98GAdInv cmp99PatchedDefectNeumannInverse
  rw [cmp98GAd_zero]
  simp only [sub_self, neg_zero]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n => simp [pow_succ]

/-- At the trivial background the nested local right-frame transport acts
as the identity on every matrix. -/
@[simp] theorem cmp98Eq119RightOuterLocalTransport_trivial
    (A : FinePhysicalOneCochain d L N' Nc)
    (b : PhysicalBond d N') (x : FinBox d (L * N'))
    (H : Matrix (Fin Nc) (Fin Nc) ℂ) :
    cmp98Eq119RightOuterLocalTransport
        (trivialPhysicalGaugeBackground d (L * N') Nc) A b x H = H := by
  unfold cmp98Eq119RightOuterLocalTransport
  simp [cmp98UbarContourFactors, fourFactorProduct]

/-- A distinguished pivot never contributes to the entrance contour, even
in the matching coarse row. -/
theorem cmp98Eq124EntrancePrefixRightVariation_single_pivot_eq_zero
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (L * N'))
    (hN' : 2 ≤ N') (hx : x ∈ blockOf L N' b.1)
    (v : SUNLieCoord Nc) :
    cmp98Eq124EntrancePrefixRightVariation U
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v)
        b x = 0 := by
  unfold cmp98Eq124EntrancePrefixRightVariation
    cmp98UbarContourFactorVariations
  simp only [Matrix.cons_val_zero]
  have hfirst :
      cmp98ContourFirstVariation U
          (singlePhysicalBondCochain
            (cmp96ConstraintPivotBond
              (d := d) (L := L) (N' := N') b) v)
          (cmp99SourceUbarGamma1 (G := SUN Nc) b x) 0 = 0 := by
    apply cmp98ContourFirstVariation_zero_of_generators
    intro e he
    apply orientedWilsonGenerator_eq_zero_of_apply_eq_zero
    exact singlePhysicalBondCochain_of_ne v
      (cmp99SourceUbarGamma1_avoids_constraintPivot
        (Nc := Nc) b b x hN' hx e he)
  rw [hfirst]
  exact zero_mul _

/-- The same distinguished pivot never contributes to the return contour. -/
theorem cmp98Eq124ExitPrefixRightVariation_single_pivot_eq_zero
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (L * N'))
    (hN' : 2 ≤ N') (hx : x ∈ blockOf L N' b.1)
    (v : SUNLieCoord Nc) :
    cmp98Eq124ExitPrefixRightVariation U
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v)
        b x = 0 := by
  unfold cmp98Eq124ExitPrefixRightVariation
  have hfirst :
      cmp98ContourFirstVariation U
          (singlePhysicalBondCochain
            (cmp96ConstraintPivotBond
              (d := d) (L := L) (N' := N') b) v)
          (cmp99SourceUbarGamma3 (G := SUN Nc) b x) 0 = 0 := by
    apply cmp98ContourFirstVariation_zero_of_generators
    intro e he
    apply orientedWilsonGenerator_eq_zero_of_apply_eq_zero
    exact singlePhysicalBondCochain_of_ne v
      (cmp99SourceUbarGamma3_avoids_constraintPivot
        (Nc := Nc) b b x hN' hx e he)
  have hvar :
      cmp98UbarContourFactorVariations U
          (singlePhysicalBondCochain
            (cmp96ConstraintPivotBond
              (d := d) (L := L) (N' := N') b) v)
          b x 2 0 = 0 := by
    simp [cmp98UbarContourFactorVariations, hfirst]
  rw [hvar]
  simp

/-- The entrance operator-minus-identity correction also vanishes on the
matching pivot probe. -/
theorem cmp98Eq119RightEntranceOperatorMinusId_single_pivot_eq_zero
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (L * N'))
    (hN' : 2 ≤ N') (hx : x ∈ blockOf L N' b.1)
    (v : SUNLieCoord Nc) :
    cmp98Eq119RightEntranceOperatorMinusId U
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v)
        b x = 0 := by
  unfold cmp98Eq119RightEntranceOperatorMinusId
  rw [cmp98Eq124EntrancePrefixRightVariation_single_pivot_eq_zero
    U b x hN' hx v]
  unfold cmp98Eq119RightOuterLocalTransport
  dsimp only
  simp only [Matrix.mul_zero, Matrix.zero_mul, sub_zero]
  rw [(cmp98GAdInv
    (nearLog (cmp98UbarAmbientDeviationMatrix U b x 0))).map_zero]
  exact (cmp98GAd (-(cmp98UbarLogAverage U b 0))).map_zero

/-- At the trivial background the middle operator-minus-identity correction
vanishes for every physical field. -/
@[simp] theorem cmp98Eq119RightMiddleOperatorMinusId_trivial
    (A : FinePhysicalOneCochain d L N' Nc)
    (b : PhysicalBond d N') (x : FinBox d (L * N')) :
    cmp98Eq119RightMiddleOperatorMinusId
        (trivialPhysicalGaugeBackground d (L * N') Nc) A b x = 0 := by
  unfold cmp98Eq119RightMiddleOperatorMinusId
  rw [cmp98Eq119RightOuterLocalTransport_trivial]
  exact sub_self _

/-- At the trivial background every local coarse-prefix contribution is the
negative of the direct coarse contribution printed after the block average. -/
theorem cmp98Eq124CoarsePrefixRightVariation_trivial_eq_neg_direct
    (A : FinePhysicalOneCochain d L N' Nc)
    (b : PhysicalBond d N') (x : FinBox d (L * N')) :
    cmp98Eq124CoarsePrefixRightVariation
        (trivialPhysicalGaugeBackground d (L * N') Nc) A b x =
      -cmp98Eq119DirectCoarseTransportedVariation
        (trivialPhysicalGaugeBackground d (L * N') Nc) A b := by
  simp [cmp98Eq124CoarsePrefixRightVariation,
    cmp98Eq119DirectCoarseTransportedVariation,
    cmp98Eq119CoarseRightVariation, cmp98UbarContourFactors]

/-- Consequently the normalized block average of the local coarse line
cancels the single direct coarse line exactly. -/
theorem cmp98Eq124_trivial_coarse_average_add_direct_eq_zero
    (A : FinePhysicalOneCochain d L N' Nc)
    (b : PhysicalBond d N') :
    ((L : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf L N' b.1,
            cmp98Eq119RightOuterLocalTransport
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x
              (cmp98Eq124CoarsePrefixRightVariation
                (trivialPhysicalGaugeBackground d (L * N') Nc) A b x) +
        cmp98Eq119DirectCoarseTransportedVariation
          (trivialPhysicalGaugeBackground d (L * N') Nc) A b = 0 := by
  rw [Finset.sum_congr rfl fun x _ =>
    (cmp98Eq119RightOuterLocalTransport_trivial A b x
      (cmp98Eq124CoarsePrefixRightVariation
        (trivialPhysicalGaugeBackground d (L * N') Nc) A b x)).trans
      (cmp98Eq124CoarsePrefixRightVariation_trivial_eq_neg_direct A b x)]
  rw [Finset.sum_const, blockOf_card,
    ← Nat.cast_smul_eq_nsmul ℝ (L ^ d),
    Nat.cast_pow]
  have hLd : (L : ℝ) ^ d ≠ 0 :=
    pow_ne_zero d (by exact_mod_cast NeZero.ne L)
  let D := cmp98Eq119DirectCoarseTransportedVariation
    (trivialPhysicalGaugeBackground d (L * N') Nc) A b
  change ((L : ℝ) ^ d)⁻¹ • ((L : ℝ) ^ d) • (-D) + D = 0
  calc
    ((L : ℝ) ^ d)⁻¹ • ((L : ℝ) ^ d) • (-D) + D =
        -D + D := congrArg (fun X => X + D)
          (inv_smul_smul₀ hLd (-D))
    _ = 0 := neg_add_cancel D

/-- On the matching pivot probe the complete printed four-line expression at
the trivial background reduces to the normalized middle line alone.  This is
the source-faithful calibration step: entrance and exit avoid the pivot, the
operator corrections vanish, and the two coarse lines cancel after the exact
block average. -/
theorem cmp98Eq124RightPrintedFourLinePhysicalVariation_single_pivot_trivial
    (b : PhysicalBond d N') (hN' : 2 ≤ N') (v : SUNLieCoord Nc) :
    cmp98Eq124RightPrintedFourLinePhysicalVariation
        (trivialPhysicalGaugeBackground d (L * N') Nc)
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v) b =
      ((L : ℝ) ^ d)⁻¹ •
        ∑ x ∈ blockOf L N' b.1,
          cmp98Eq124MiddlePrefixRightVariation
            (trivialPhysicalGaugeBackground d (L * N') Nc)
            (singlePhysicalBondCochain
              (cmp96ConstraintPivotBond
                (d := d) (L := L) (N' := N') b) v) b x := by
  let A : FinePhysicalOneCochain d L N' Nc :=
    singlePhysicalBondCochain
      (cmp96ConstraintPivotBond
        (d := d) (L := L) (N' := N') b) v
  change cmp98Eq124RightPrintedFourLinePhysicalVariation
      (trivialPhysicalGaugeBackground d (L * N') Nc) A b =
    ((L : ℝ) ^ d)⁻¹ •
      ∑ x ∈ blockOf L N' b.1,
        cmp98Eq124MiddlePrefixRightVariation
          (trivialPhysicalGaugeBackground d (L * N') Nc) A b x
  unfold cmp98Eq124RightPrintedFourLinePhysicalVariation
  have hlocal :
      ∀ x ∈ blockOf L N' b.1,
        (cmp98Eq124MiddlePrefixRightVariation
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x +
            cmp98Eq119RightEntranceOperatorMinusId
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x +
            cmp98Eq119RightMiddleOperatorMinusId
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x +
            (cmp98Eq119RightOuterLocalTransport
                (trivialPhysicalGaugeBackground d (L * N') Nc) A b x
                  (cmp98Eq124ExitPrefixRightVariation
                    (trivialPhysicalGaugeBackground d (L * N') Nc) A b x) -
              cmp98Eq124ExitPrefixRightVariation
                (trivialPhysicalGaugeBackground d (L * N') Nc) A b x) +
            cmp98Eq119RightOuterLocalTransport
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x
                (cmp98Eq124CoarsePrefixRightVariation
                  (trivialPhysicalGaugeBackground d (L * N') Nc) A b x)) =
          cmp98Eq124MiddlePrefixRightVariation
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x +
            cmp98Eq119RightOuterLocalTransport
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x
                (cmp98Eq124CoarsePrefixRightVariation
                  (trivialPhysicalGaugeBackground d (L * N') Nc) A b x) := by
    intro x hx
    rw [cmp98Eq119RightEntranceOperatorMinusId_single_pivot_eq_zero
      (trivialPhysicalGaugeBackground d (L * N') Nc) b x hN' hx v,
      cmp98Eq119RightMiddleOperatorMinusId_trivial,
      cmp98Eq124ExitPrefixRightVariation_single_pivot_eq_zero
        (trivialPhysicalGaugeBackground d (L * N') Nc) b x hN' hx v]
    rw [cmp98Eq119RightOuterLocalTransport_trivial]
    simp
  rw [Finset.sum_congr rfl hlocal, Finset.sum_add_distrib]
  have hsplit :
      ((L : ℝ) ^ d)⁻¹ •
          ((∑ x ∈ blockOf L N' b.1,
              cmp98Eq124MiddlePrefixRightVariation
                (trivialPhysicalGaugeBackground d (L * N') Nc) A b x) +
            ∑ x ∈ blockOf L N' b.1,
              cmp98Eq119RightOuterLocalTransport
                (trivialPhysicalGaugeBackground d (L * N') Nc) A b x
                  (cmp98Eq124CoarsePrefixRightVariation
                    (trivialPhysicalGaugeBackground d (L * N') Nc) A b x)) =
        ((L : ℝ) ^ d)⁻¹ •
            ∑ x ∈ blockOf L N' b.1,
              cmp98Eq124MiddlePrefixRightVariation
                (trivialPhysicalGaugeBackground d (L * N') Nc) A b x +
          ((L : ℝ) ^ d)⁻¹ •
            ∑ x ∈ blockOf L N' b.1,
              cmp98Eq119RightOuterLocalTransport
                (trivialPhysicalGaugeBackground d (L * N') Nc) A b x
                  (cmp98Eq124CoarsePrefixRightVariation
                    (trivialPhysicalGaugeBackground d (L * N') Nc) A b x) := by
    ext i j
    simp [Matrix.smul_apply, Matrix.add_apply, mul_add]
  rw [hsplit]
  calc
    ((L : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf L N' b.1,
            cmp98Eq124MiddlePrefixRightVariation
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x +
        ((L : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf L N' b.1,
            cmp98Eq119RightOuterLocalTransport
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x
                (cmp98Eq124CoarsePrefixRightVariation
                  (trivialPhysicalGaugeBackground d (L * N') Nc) A b x) +
        cmp98Eq119DirectCoarseTransportedVariation
          (trivialPhysicalGaugeBackground d (L * N') Nc) A b =
      ((L : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf L N' b.1,
            cmp98Eq124MiddlePrefixRightVariation
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x +
        (((L : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf L N' b.1,
            cmp98Eq119RightOuterLocalTransport
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x
                (cmp98Eq124CoarsePrefixRightVariation
                  (trivialPhysicalGaugeBackground d (L * N') Nc) A b x) +
        cmp98Eq119DirectCoarseTransportedVariation
          (trivialPhysicalGaugeBackground d (L * N') Nc) A b) := by abel
    _ = ((L : ℝ) ^ d)⁻¹ •
          ∑ x ∈ blockOf L N' b.1,
            cmp98Eq124MiddlePrefixRightVariation
              (trivialPhysicalGaugeBackground d (L * N') Nc) A b x := by
      rw [cmp98Eq124_trivial_coarse_average_add_direct_eq_zero A b, add_zero]

/-- Removing the additional `L⁻¹` normalization from the already-proved
(124)--(125) dictionary identifies the raw middle line at the trivial
background with the literal flat block constraint matrix. -/
theorem cmp98Eq124RightRawMainLine_trivial_eq_flatBlockConstraint
    (A : FinePhysicalOneCochain d L N' Nc)
    (b : PhysicalBond d N') :
    cmp98Eq124RightRawMainLine
        (trivialPhysicalGaugeBackground d (L * N') Nc) A b =
      cmp98LieCoordMatrix
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A b) := by
  have hmain :=
    cmp98Eq124RightMainLine_eq_eq125MainAverageValue
      (trivialPhysicalGaugeBackground d (L * N') Nc) A b
  have hflat :=
    cmp98Eq125MainAverageCLM_trivial_apply
      (matrixSUNAdjointModel Nc) A b
  rw [cmp98Eq125MainAverageCLM_apply] at hflat
  rw [cmp98Eq124RightMainLine, hflat,
    cmp98LieCoordMatrix_smul] at hmain
  ext i j
  have hij := congrFun (congrFun hmain i) j
  simp only [Matrix.smul_apply, Complex.real_smul] at hij
  push_cast at hij
  have hL : ((L : ℝ)⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (by exact_mod_cast NeZero.ne L : (L : ℝ) ≠ 0)
  exact mul_left_cancel₀ hL hij

/-- The endpoint conjugation of (120) is absent on the distinguished pivot:
both of its contour derivatives avoid that bond. -/
theorem cmp98Eq120PhysicalEndpointCorrection_single_pivot_eq_zero
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (b : PhysicalBond d N') (hN' : 2 ≤ N') (v : SUNLieCoord Nc) :
    cmp98Eq120PhysicalEndpointCorrection U
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v) b = 0 := by
  unfold cmp98Eq120PhysicalEndpointCorrection
  apply smul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro x hx
  rw [cmp98Eq124EntrancePrefixRightVariation_single_pivot_eq_zero
      U b x hN' hx v,
    cmp98Eq124ExitPrefixRightVariation_single_pivot_eq_zero
      U b x hN' hx v]
  simp

/-- At the trivial background the literal nonlinear right variation on the
pivot probe is exactly the printed four-line expression.  The passage uses the
source-derived four-contour formula and the just-proved vanishing of the
endpoint correction. -/
theorem cmp98Eq119NonlinearRightVariation_single_pivot_trivial_eq_printed
    (b : PhysicalBond d N') (hN' : 2 ≤ N') (v : SUNLieCoord Nc) :
    cmp98Eq119NonlinearRightVariation
        (trivialPhysicalGaugeBackground d (L * N') Nc)
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v) b =
      cmp98Eq124RightPrintedFourLinePhysicalVariation
        (trivialPhysicalGaugeBackground d (L * N') Nc)
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v) b := by
  let U := trivialPhysicalGaugeBackground d (L * N') Nc
  let A : FinePhysicalOneCochain d L N' Nc :=
    singlePhysicalBondCochain
      (cmp96ConstraintPivotBond
        (d := d) (L := L) (N' := N') b) v
  change cmp98Eq119NonlinearRightVariation U A b =
    cmp98Eq124RightPrintedFourLinePhysicalVariation U A b
  have hthird :
      ∀ x ∈ blockOf L N' b.1,
        ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ (1 : ℝ) / 3 := by
    intro x hx
    simp [U]
  calc
    cmp98Eq119NonlinearRightVariation U A b =
        cmp98Eq119RightFourSourcePhysicalVariation U A b +
          cmp98Eq119DirectCoarseTransportedVariation U A b :=
      cmp98Eq119NonlinearRightVariation_eq_fourSources_add_direct
        U A b hthird
    _ = cmp98Eq120RightAssembledPhysicalVariation U A b := by
      unfold cmp98Eq120RightAssembledPhysicalVariation
      rw [cmp98Eq120PhysicalEndpointCorrection_single_pivot_eq_zero
        U b hN' v, add_zero]
    _ = cmp98Eq124RightPrintedFourLinePhysicalVariation U A b :=
      cmp98Eq120RightAssembledPhysicalVariation_eq_fourLine U A b

/-- The literal ambient Fréchet derivative used by CMP109 therefore equals
the same printed matrix on the flat pivot probe. -/
theorem fderiv_cmp102AmbientNonlinearBlock_single_pivot_trivial_eq_printed
    (b : PhysicalBond d N') (hN' : 2 ≤ N') (v : SUNLieCoord Nc) :
    fderiv ℝ
          (cmp102AmbientNonlinearBlock
            (trivialPhysicalGaugeBackground d (L * N') Nc) b) 0
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent
              (singlePhysicalBondCochain
                (cmp96ConstraintPivotBond
                  (d := d) (L := L) (N' := N') b) v))) *
        cmp98Eq119NonlinearBlockInverseAtZero
          (trivialPhysicalGaugeBackground d (L * N') Nc)
          (0 : FinePhysicalOneCochain d L N' Nc) b =
      cmp98Eq124RightPrintedFourLinePhysicalVariation
        (trivialPhysicalGaugeBackground d (L * N') Nc)
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v) b := by
  let U := trivialPhysicalGaugeBackground d (L * N') Nc
  let A : FinePhysicalOneCochain d L N' Nc :=
    singlePhysicalBondCochain
      (cmp96ConstraintPivotBond
        (d := d) (L := L) (N' := N') b) v
  have hsmall :
      ∀ x ∈ blockOf L N' b.1,
        ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1 := by
    intro x hx
    simp [U]
  have hambient :=
    cmp98Eq119NonlinearRightVariation_eq_ambientFDeriv U A b hsmall
  change
    fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) *
        cmp98Eq119NonlinearBlockInverseAtZero U
          (0 : FinePhysicalOneCochain d L N' Nc) b =
      cmp98Eq124RightPrintedFourLinePhysicalVariation U A b
  calc
    fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) *
        cmp98Eq119NonlinearBlockInverseAtZero U
          (0 : FinePhysicalOneCochain d L N' Nc) b =
      fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) := by
        rw [cmp98Eq119NonlinearBlockInverseAtZero_trivial, mul_one]
    _ = fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) *
        cmp98Eq119NonlinearBlockInverseAtZero U A b := by
      rw [cmp98Eq119NonlinearBlockInverseAtZero_trivial, mul_one]
    _ = cmp98Eq119NonlinearRightVariation U A b := hambient.symm
    _ = cmp98Eq124RightPrintedFourLinePhysicalVariation U A b :=
      cmp98Eq119NonlinearRightVariation_single_pivot_trivial_eq_printed
        b hN' v

/-- The complete printed matrix on the flat pivot probe is exactly the matrix
representative of the ordinary flat block constraint. -/
theorem cmp98Eq124RightPrintedFourLinePhysicalVariation_single_pivot_trivial_eq_flat
    (b : PhysicalBond d N') (hN' : 2 ≤ N') (v : SUNLieCoord Nc) :
    cmp98Eq124RightPrintedFourLinePhysicalVariation
        (trivialPhysicalGaugeBackground d (L * N') Nc)
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v) b =
      cmp98LieCoordMatrix
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
          (singlePhysicalBondCochain
            (cmp96ConstraintPivotBond
              (d := d) (L := L) (N' := N') b) v) b) := by
  rw [cmp98Eq124RightPrintedFourLinePhysicalVariation_single_pivot_trivial
    b hN' v]
  change cmp98Eq124RightRawMainLine
      (trivialPhysicalGaugeBackground d (L * N') Nc)
      (singlePhysicalBondCochain
        (cmp96ConstraintPivotBond
          (d := d) (L := L) (N' := N') b) v) b =
    cmp98LieCoordMatrix
      (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v) b)
  exact cmp98Eq124RightRawMainLine_trivial_eq_flatBlockConstraint _ b

/-- The canonical ambient retraction is a left inverse of the repository
coordinate-to-matrix dictionary. -/
@[simp] theorem cmp98AmbientToLieCoordCLM_apply_lieCoordMatrix
    (X : SUNLieCoord Nc) :
    cmp98AmbientToLieCoordCLM Nc (cmp98LieCoordMatrix X) = X := by
  unfold cmp98LieCoordMatrix
  rw [cmp98AmbientToLieCoordCLM_apply_mem]
  exact (suLieCoordIso Nc).apply_symm_apply X

/-- Matching diagonal calibration of the literal physical constraint: on a
single distinguished pivot at the trivial background it is exactly the flat
block constraint, with no hidden coefficient. -/
theorem cmp109PhysicalLinearConstraint_single_constraintPivot_trivial
    (b : PhysicalBond d N') (hN' : 2 ≤ N') (v : SUNLieCoord Nc) :
    cmp109PhysicalLinearConstraint
        (trivialPhysicalGaugeBackground d (L * N') Nc)
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v) b =
      flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b) v) b := by
  rw [cmp109PhysicalLinearConstraint_apply,
    cmp102PhysicalCochainToAmbientCLM_apply]
  have hderiv :=
    fderiv_cmp102AmbientNonlinearBlock_single_pivot_trivial_eq_printed
      (d := d) (L := L) (N' := N') (Nc := Nc) b hN' v
  calc
    cmp98AmbientToLieCoordCLM Nc
        (fderiv ℝ
            (cmp102AmbientNonlinearBlock
              (trivialPhysicalGaugeBackground d (L * N') Nc) b) 0
            (physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent
                (singlePhysicalBondCochain
                  (cmp96ConstraintPivotBond
                    (d := d) (L := L) (N' := N') b) v))) *
          cmp98Eq119NonlinearBlockInverseAtZero
            (trivialPhysicalGaugeBackground d (L * N') Nc)
            (0 : FinePhysicalOneCochain d L N' Nc) b) =
      cmp98AmbientToLieCoordCLM Nc
        (cmp98Eq124RightPrintedFourLinePhysicalVariation
          (trivialPhysicalGaugeBackground d (L * N') Nc)
          (singlePhysicalBondCochain
            (cmp96ConstraintPivotBond
              (d := d) (L := L) (N' := N') b) v) b) :=
        congrArg (cmp98AmbientToLieCoordCLM Nc) hderiv
    _ = flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
          (singlePhysicalBondCochain
            (cmp96ConstraintPivotBond
              (d := d) (L := L) (N' := N') b) v) b := by
      rw [cmp98Eq124RightPrintedFourLinePhysicalVariation_single_pivot_trivial_eq_flat
        (d := d) (L := L) (N' := N') (Nc := Nc) b hN' v,
        cmp98AmbientToLieCoordCLM_apply_lieCoordMatrix]

/-- The physical pivot response is exactly the identity at the trivial
background.  Off-diagonal terms vanish by contour geometry; the matching term
is calibrated above and the sparse insertion carries precisely the inverse
flat scaling. -/
theorem cmp109PhysicalPivotResponseCLM_trivial_apply
    (hN' : 2 ≤ N') (D : CoarsePhysicalOneCochain d N' Nc) :
    cmp109PhysicalPivotResponseCLM
        (trivialPhysicalGaugeBackground d (L * N') Nc) D = D := by
  apply PiLp.ext
  intro b
  have hsmall :
      ∀ c : PhysicalBond d N', ∀ x ∈ blockOf L N' c.1,
        ‖cmp98UbarAmbientDeviationMatrix
          (trivialPhysicalGaugeBackground d (L * N') Nc) c x 0‖ < 1 := by
    intro c x hx
    simp
  rw [cmp109PhysicalPivotResponseCLM_apply_eq_diagonal
      (trivialPhysicalGaugeBackground d (L * N') Nc) hN' hsmall D b,
    cmp109PhysicalLinearConstraint_single_constraintPivot_trivial
      (d := d) (L := L) (N' := N') (Nc := Nc) b hN'
        (((L : ℝ) ^ (d - 1)) • D b),
    flatBlockConstraint_pivot_probe_apply, if_pos rfl]
  rw [smul_smul, smul_smul]
  rw [mul_assoc]
  rw [cmp96ConstraintPivot_scale_cancel, one_smul]

/-- Bundled flat calibration of the complete physical pivot response. -/
theorem cmp109PhysicalPivotResponseCLM_trivial
    (hN' : 2 ≤ N') :
    cmp109PhysicalPivotResponseCLM
        (trivialPhysicalGaugeBackground d (L * N') Nc) =
      ContinuousLinearMap.id ℝ
        (CoarsePhysicalOneCochain d N' Nc) := by
  apply ContinuousLinearMap.ext
  intro D
  exact cmp109PhysicalPivotResponseCLM_trivial_apply hN' D

/-- Hence the named physical pivot defect is literally zero at the flat
background.  This calibrates, but does not replace, the quantitative
contraction proof still required for small interacting backgrounds. -/
theorem cmp109PhysicalPivotDefectCLM_trivial
    (hN' : 2 ≤ N') :
    cmp109PhysicalPivotDefectCLM
        (trivialPhysicalGaugeBackground d (L * N') Nc) = 0 := by
  unfold cmp109PhysicalPivotDefectCLM
  rw [cmp109PhysicalPivotResponseCLM_trivial hN']
  exact sub_self _

/-- The flat defect therefore satisfies the Neumann condition with maximal
margin. -/
theorem norm_cmp109PhysicalPivotDefectCLM_trivial_lt_one
    (hN' : 2 ≤ N') :
    ‖cmp109PhysicalPivotDefectCLM
        (trivialPhysicalGaugeBackground d (L * N') Nc)‖ < 1 := by
  rw [cmp109PhysicalPivotDefectCLM_trivial hN', norm_zero]
  norm_num

end

end YangMills.RG
