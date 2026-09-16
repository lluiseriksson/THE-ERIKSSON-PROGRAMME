/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98ContourPivotAvoidance
import YangMills.RG.BalabanCMP102AmbientNonlinearBlockFDeriv
import YangMills.RG.BalabanCMP102PhysicalFirstVariationBound
import YangMills.RG.BalabanCMP109PhysicalLinearConstraint

/-!
# Exact off-diagonal vanishing of the physical CMP109 pivot response

The literal four-contour word in coarse row `b` avoids the distinguished
pivot bond `b₀(c)` whenever `b ≠ c`.  This file propagates that geometric
fact through:

* the ordered contour derivative;
* the logarithmic block average;
* its outer exponential;
* the represented nonlinear block;
* the canonical `su(N)` coordinate transport.

The terminal theorem says that the physical linear constraint in row `b`
vanishes on a single probe at the nonmatching pivot `b₀(c)`.  It is the
source-facing no-mixing statement needed to prove that the pivot response
and its inverse are pointwise in the coarse bond.  No diagonal certificate,
kernel estimate, or abstract support hypothesis is supplied.

Crucially, pointwise does **not** mean identity: the matching diagonal block
remains the background-dependent derivative coefficient printed in CMP109.
Thus this theorem does not prove `cmp109PhysicalPivotDefectCLM U = 0` and does
not remove the need to invert the matching pivot response (by a pointwise
inverse or by the existing Neumann construction).

The condition `2 ≤ N'` is explicit.  It excludes the one-cell coarse torus,
where the source and target blocks of a coarse bond coincide.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 2000000

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]

/-- A probe at a nonmatching distinguished pivot has zero first variation
on the complete four-contour deviation. -/
theorem cmp98UbarDeviationFirstVariation_zero_single_constraintPivot_of_ne
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (b c : PhysicalBond d N') (hbc : b ≠ c)
    (x : FinBox d (L * N')) (hN' : 2 ≤ N')
    (hx : x ∈ blockOf L N' b.1) (v : SUNLieCoord Nc) :
    cmp98UbarDeviationFirstVariation U
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') c) v)
        b x 0 = 0 := by
  rw [cmp98UbarDeviationFirstVariation_zero_eq_sourceContour]
  apply cmp98ContourFirstVariation_zero_of_generators
  intro e he
  apply orientedWilsonGenerator_eq_zero_of_apply_eq_zero
  exact singlePhysicalBondCochain_of_ne v
    (cmp98SourceFourContourEdges_avoids_constraintPivot_of_ne
      (Nc := Nc) b c hbc x hN' hx e he)

/-- The physical logarithmic block variation has no off-diagonal pivot
response. -/
theorem cmp98UbarLogAveragePhysicalVariation_single_constraintPivot_eq_zero
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (b c : PhysicalBond d N') (hbc : b ≠ c)
    (hN' : 2 ≤ N') (v : SUNLieCoord Nc) :
    cmp98UbarLogAveragePhysicalVariation U
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') c) v)
        b = 0 := by
  unfold cmp98UbarLogAveragePhysicalVariation
  apply smul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro x hx
  rw [cmp98UbarDeviationFirstVariation_zero_single_constraintPivot_of_ne
    U b c hbc x hN' hx v]
  exact (∑' n : ℕ,
    nearLogTermFDeriv
      (cmp98UbarAmbientDeviationMatrix U b x 0) n).map_zero

/-- The derivative of the outer exponential also has no off-diagonal pivot
response. -/
theorem fderiv_cmp98UbarExpAverage_zero_apply_single_constraintPivot_of_ne
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (b c : PhysicalBond d N') (hbc : b ≠ c)
    (hN' : 2 ≤ N') (v : SUNLieCoord Nc)
    (hsmall : ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    fderiv ℝ (cmp98UbarExpAverage U b) 0
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent
            (singlePhysicalBondCochain
              (cmp96ConstraintPivotBond
                (d := d) (L := L) (N' := N') c) v))) = 0 := by
  rw [fderiv_cmp98UbarExpAverage_zero_apply_physical U
    (singlePhysicalBondCochain
      (cmp96ConstraintPivotBond
        (d := d) (L := L) (N' := N') c) v) b hsmall]
  rw [cmp98UbarLogAveragePhysicalVariation_single_constraintPivot_eq_zero
    U b c hbc hN' v]
  exact
    (fderiv ℝ
      (NormedSpace.exp : Matrix (Fin Nc) (Fin Nc) ℂ →
        Matrix (Fin Nc) (Fin Nc) ℂ)
      (cmp98UbarLogAverage U b 0)).map_zero

/-- The straight coarse contour in a nonmatching row has zero derivative
on the distinguished pivot probe. -/
theorem fderiv_cmp98SourceCoarseBondPath_zero_apply_single_constraintPivot_of_ne
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (b c : PhysicalBond d N') (hbc : b ≠ c)
    (v : SUNLieCoord Nc) :
    fderiv ℝ
        (fun Z => cmp98AmbientWilsonLineMatrix U Z
          (cmp98SourceCoarseBondPath (Nc := Nc) (M := L) b)) 0
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent
            (singlePhysicalBondCochain
              (cmp96ConstraintPivotBond
                (d := d) (L := L) (N' := N') c) v))) = 0 := by
  exact fderiv_cmp98AmbientWilsonLineMatrix_zero_apply_single_of_avoids
    U
    (cmp96ConstraintPivotBond
      (d := d) (L := L) (N' := N') c)
    v
    (cmp98SourceCoarseBondPath (Nc := Nc) (M := L) b)
    (cmp98SourceCoarseBondPath_avoids_constraintPivot_of_ne
      (Nc := Nc) b c hbc)

/-- The raw represented-block derivative is exactly zero on a nonmatching
pivot probe. -/
theorem fderiv_cmp102AmbientNonlinearBlock_zero_apply_single_constraintPivot_of_ne
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (b c : PhysicalBond d N') (hbc : b ≠ c)
    (hN' : 2 ≤ N') (v : SUNLieCoord Nc)
    (hsmall : ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent
            (singlePhysicalBondCochain
              (cmp96ConstraintPivotBond
                (d := d) (L := L) (N' := N') c) v))) = 0 := by
  let A : PhysicalGaugeOneCochain d (L * N') Nc :=
    singlePhysicalBondCochain
      (cmp96ConstraintPivotBond
        (d := d) (L := L) (N' := N') c) v
  let H : PhysicalAmbientMatrixTangent d (L * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  rw [fderiv_cmp102AmbientNonlinearBlock_apply U b 0 H hsmall]
  have houter :
      fderiv ℝ (cmp98UbarExpAverage U b) 0 H = 0 := by
    simpa [A, H] using
      fderiv_cmp98UbarExpAverage_zero_apply_single_constraintPivot_of_ne
        U b c hbc hN' v hsmall
  have hcoarse :
      fderiv ℝ
          (fun Z => cmp98AmbientWilsonLineMatrix U Z
            (cmp98SourceCoarseBondPath (Nc := Nc) (M := L) b)) 0 H = 0 := by
    simpa [A, H] using
      fderiv_cmp98SourceCoarseBondPath_zero_apply_single_constraintPivot_of_ne
        U b c hbc v
  rw [houter, hcoarse]
  simp

/-- Terminal no-mixing theorem: the physical `L Q̃_U` row `b` vanishes on
the distinguished pivot probe belonging to every other coarse row `c`. -/
theorem cmp109PhysicalLinearConstraint_single_constraintPivot_apply_of_ne
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (b c : PhysicalBond d N') (hbc : b ≠ c)
    (hN' : 2 ≤ N') (v : SUNLieCoord Nc)
    (hsmall : ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp109PhysicalLinearConstraint U
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') c) v)
        b = 0 := by
  rw [cmp109PhysicalLinearConstraint_apply]
  have hzero :
      fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
          (cmp102PhysicalCochainToAmbientCLM
            (singlePhysicalBondCochain
              (cmp96ConstraintPivotBond
                (d := d) (L := L) (N' := N') c) v)) = 0 := by
    rw [cmp102PhysicalCochainToAmbientCLM_apply]
    exact
      fderiv_cmp102AmbientNonlinearBlock_zero_apply_single_constraintPivot_of_ne
        U b c hbc hN' v hsmall
  have hmul :
      fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
          (cmp102PhysicalCochainToAmbientCLM
            (singlePhysicalBondCochain
              (cmp96ConstraintPivotBond
                (d := d) (L := L) (N' := N') c) v)) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b = 0 := by
    exact (congrArg
      (fun X : Matrix (Fin Nc) (Fin Nc) ℂ =>
        X * cmp98Eq119NonlinearBlockInverseAtZero U
          (0 : FinePhysicalOneCochain d L N' Nc) b) hzero).trans (zero_mul _)
  exact (congrArg (cmp98AmbientToLieCoordCLM Nc) hmul).trans
    (cmp98AmbientToLieCoordCLM Nc).map_zero

/-- The complete physical pivot response is pointwise in the coarse bond:
its value in row `b` is obtained solely from the matching pivot summand.
This is the exact diagonal decomposition, derived from the literal contours
rather than supplied as an operator certificate. -/
theorem cmp109PhysicalPivotResponseCLM_apply_eq_diagonal
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hN' : 2 ≤ N')
    (hsmall : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf L N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1)
    (D : CoarsePhysicalOneCochain d N' Nc)
    (b : PhysicalBond d N') :
    cmp109PhysicalPivotResponseCLM U D b =
      cmp109PhysicalLinearConstraint U
        (singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') b)
          (((L : ℝ) ^ (d - 1)) • D b))
        b := by
  rw [cmp109PhysicalPivotResponseCLM_apply]
  unfold cmp96ConstraintPivotInsertion
  change
    (cmp109PhysicalLinearConstraintCLM U
      (∑ c : PhysicalBond d N',
        singlePhysicalBondCochain
          (cmp96ConstraintPivotBond
            (d := d) (L := L) (N' := N') c)
          (((L : ℝ) ^ (d - 1)) • D c))) b = _
  rw [map_sum]
  let f : PhysicalBond d N' → CoarsePhysicalOneCochain d N' Nc := fun c =>
    cmp109PhysicalLinearConstraint U
      (singlePhysicalBondCochain
        (cmp96ConstraintPivotBond
          (d := d) (L := L) (N' := N') c)
        (((L : ℝ) ^ (d - 1)) • D c))
  change (∑ c : PhysicalBond d N', f c) b = f b b
  have eval_sum (s : Finset (PhysicalBond d N')) :
      (∑ c ∈ s, f c) b = ∑ c ∈ s, f c b := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert c s hc ih =>
        rw [Finset.sum_insert hc, Finset.sum_insert hc, PiLp.add_apply, ih]
  rw [eval_sum Finset.univ]
  classical
  rw [Finset.sum_eq_single b]
  · intro c _hc hcb
    exact cmp109PhysicalLinearConstraint_single_constraintPivot_apply_of_ne
      U b c (Ne.symm hcb) hN'
      (((L : ℝ) ^ (d - 1)) • D c) (hsmall b)
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ b))

end

end YangMills.RG
