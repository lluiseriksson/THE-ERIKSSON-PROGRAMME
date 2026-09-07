/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109PhysicalPivotNoMixing
import YangMills.RG.BalabanCMP109PhysicalConstraintRightInverseSupport

/-!
# No coarse-bond mixing in the CMP109 pivot inverse

The literal contour geometry makes the physical pivot response pointwise in
the coarse bond.  This module propagates that source-derived fact through the
named defect, every power in its Neumann series, and the resulting inverse.

Consequently the value of the physical constraint right inverse on the pivot
bond `b₀(c)` depends only on the matching coarse datum `D(c)`.  This removes the
old source-locality obligation from the right-inverse construction without
claiming that the matching diagonal block is the identity or that its defect
is small.  The contraction estimate remains a visible physical obligation.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- Equality of the input at one coarse bond is preserved by the literal
physical pivot response at that bond. -/
theorem cmp109PhysicalPivotResponseCLM_apply_congr
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hN' : 2 ≤ N')
    (hsmall : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    {D E : CoarsePhysicalOneCochain d N' Nc}
    (b : PhysicalBond d N')
    (hDE : D b = E b) :
    cmp109PhysicalPivotResponseCLM U D b =
      cmp109PhysicalPivotResponseCLM U E b := by
  rw [cmp109PhysicalPivotResponseCLM_apply_eq_diagonal U hN' hsmall D b,
    cmp109PhysicalPivotResponseCLM_apply_eq_diagonal U hN' hsmall E b,
    hDE]

/-- The named physical pivot defect is pointwise in the same coarse bond. -/
theorem cmp109PhysicalPivotDefectCLM_apply_congr
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hN' : 2 ≤ N')
    (hsmall : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    {D E : CoarsePhysicalOneCochain d N' Nc}
    (b : PhysicalBond d N')
    (hDE : D b = E b) :
    cmp109PhysicalPivotDefectCLM U D b =
      cmp109PhysicalPivotDefectCLM U E b := by
  simp only [cmp109PhysicalPivotDefectCLM, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, PiLp.sub_apply]
  rw [cmp109PhysicalPivotResponseCLM_apply_congr U hN' hsmall b hDE, hDE]

/-- Every term of the physical defect-Neumann series remains pointwise in the
coarse bond. -/
theorem cmp109PhysicalPivotDefect_neg_pow_apply_congr
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hN' : 2 ≤ N')
    (hsmall : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (n : ℕ)
    {D E : CoarsePhysicalOneCochain d N' Nc}
    (b : PhysicalBond d N')
    (hDE : D b = E b) :
    ((-cmp109PhysicalPivotDefectCLM U) ^ n) D b =
      ((-cmp109PhysicalPivotDefectCLM U) ^ n) E b := by
  induction n generalizing D E with
  | zero =>
      simpa using hDE
  | succ n ih =>
      change
        (((-cmp109PhysicalPivotDefectCLM U) ^ n).comp
          (-cmp109PhysicalPivotDefectCLM U) D) b =
        (((-cmp109PhysicalPivotDefectCLM U) ^ n).comp
          (-cmp109PhysicalPivotDefectCLM U) E) b
      simp only [ContinuousLinearMap.comp_apply]
      apply ih
      simp only [ContinuousLinearMap.neg_apply, PiLp.neg_apply, neg_inj]
      exact cmp109PhysicalPivotDefectCLM_apply_congr
        U hN' hsmall b hDE

/-- The convergent physical pivot inverse does not mix coarse bonds. -/
theorem cmp109PhysicalPivotInverseCLM_apply_congr
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hN' : 2 ≤ N')
    (hbackground : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (hdefect : ‖cmp109PhysicalPivotDefectCLM U‖ < 1)
    {D E : CoarsePhysicalOneCochain d N' Nc}
    (b : PhysicalBond d N')
    (hDE : D b = E b) :
    cmp109PhysicalPivotInverseCLM U D b =
      cmp109PhysicalPivotInverseCLM U E b := by
  let X := CoarsePhysicalOneCochain d N' Nc
  let evalAt (F : X) : SUNLieCoord Nc := F b
  let evalCLM : (X →L[ℝ] X) →L[ℝ] SUNLieCoord Nc :=
    ((ContinuousLinearMap.proj b).comp
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : PhysicalBond d N' => SUNLieCoord Nc)).toContinuousLinearMap).comp
      (ContinuousLinearMap.apply ℝ X D)
  let evalCLME : (X →L[ℝ] X) →L[ℝ] SUNLieCoord Nc :=
    ((ContinuousLinearMap.proj b).comp
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : PhysicalBond d N' => SUNLieCoord Nc)).toContinuousLinearMap).comp
      (ContinuousLinearMap.apply ℝ X E)
  have hsum :
      Summable (fun n : ℕ => (-cmp109PhysicalPivotDefectCLM U) ^ n) :=
    summable_cmp99PatchedDefectNeumannInverse hdefect
  have hmapD := evalCLM.map_tsum hsum
  have hmapE := evalCLME.map_tsum hsum
  rw [cmp109PhysicalPivotInverseCLM,
    cmp99PatchedDefectNeumannInverse]
  change evalAt ((∑' n : ℕ, (-cmp109PhysicalPivotDefectCLM U) ^ n) D) =
    evalAt ((∑' n : ℕ, (-cmp109PhysicalPivotDefectCLM U) ^ n) E)
  rw [show evalAt ((∑' n : ℕ, (-cmp109PhysicalPivotDefectCLM U) ^ n) D) =
      ∑' n : ℕ, evalAt (((-cmp109PhysicalPivotDefectCLM U) ^ n) D) by
        simpa [evalAt, evalCLM] using hmapD,
    show evalAt ((∑' n : ℕ, (-cmp109PhysicalPivotDefectCLM U) ^ n) E) =
      ∑' n : ℕ, evalAt (((-cmp109PhysicalPivotDefectCLM U) ^ n) E) by
        simpa [evalAt, evalCLME] using hmapE]
  apply tsum_congr
  intro n
  exact cmp109PhysicalPivotDefect_neg_pow_apply_congr
    U hN' hbackground n b hDE

/-- A zero matching input coordinate gives a zero matching coordinate after
the physical pivot inverse. -/
theorem cmp109PhysicalPivotInverseCLM_apply_eq_zero
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hN' : 2 ≤ N')
    (hbackground : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (hdefect : ‖cmp109PhysicalPivotDefectCLM U‖ < 1)
    (D : CoarsePhysicalOneCochain d N' Nc)
    (b : PhysicalBond d N')
    (hDb : D b = 0) :
    cmp109PhysicalPivotInverseCLM U D b = 0 := by
  have hcongr := cmp109PhysicalPivotInverseCLM_apply_congr
    U hN' hbackground hdefect b
    (E := (0 : CoarsePhysicalOneCochain d N' Nc)) (by simpa using hDb)
  simpa using hcongr

/-- At the literal pivot bond `b₀(c)`, the constructed physical constraint
right inverse depends only on the matching coarse datum `D(c)`. -/
theorem cmp109PhysicalConstraintRightInverseCLM_apply_pivot_congr
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hN' : 2 ≤ N')
    (hbackground : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (hdefect : ‖cmp109PhysicalPivotDefectCLM U‖ < 1)
    {D E : CoarsePhysicalOneCochain d N' Nc}
    (c : PhysicalBond d N')
    (hDE : D c = E c) :
    cmp109PhysicalConstraintRightInverseCLM U D
        (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c) =
      cmp109PhysicalConstraintRightInverseCLM U E
        (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c) := by
  rw [cmp109PhysicalConstraintRightInverseCLM_apply_pivot,
    cmp109PhysicalConstraintRightInverseCLM_apply_pivot,
    cmp109PhysicalPivotInverseCLM_apply_congr
      U hN' hbackground hdefect c hDE]

/-- If the matching coarse datum vanishes, the physical right inverse also
vanishes on its matching pivot bond. -/
theorem cmp109PhysicalConstraintRightInverseCLM_apply_pivot_eq_zero
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hN' : 2 ≤ N')
    (hbackground : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (hdefect : ‖cmp109PhysicalPivotDefectCLM U‖ < 1)
    (D : CoarsePhysicalOneCochain d N' Nc)
    (c : PhysicalBond d N')
    (hDc : D c = 0) :
    cmp109PhysicalConstraintRightInverseCLM U D
        (cmp96ConstraintPivotBond (d := d) (L := L) (N' := N') c) = 0 := by
  rw [cmp109PhysicalConstraintRightInverseCLM_apply_pivot,
    cmp109PhysicalPivotInverseCLM_apply_eq_zero
      U hN' hbackground hdefect D c hDc, smul_zero]

end

end YangMills.RG
