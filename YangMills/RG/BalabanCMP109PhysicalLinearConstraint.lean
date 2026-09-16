/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalIntrinsicCorrectionAnalytic
import YangMills.RG.BalabanCMP96ConstraintRightInverse

/-!
# The physical `L Q̃` constraint in CMP109 coordinates

CMP109 linearizes the represented nonlinear block constraint before removing
one pivot bond per coarse bond.  The operator which the source asks `h` to
right-invert is `L Q̃`, not the unscaled `Q̃`; it is exactly the raw Fréchet
derivative at zero of the same represented block used by the nonlinear
correction, right-normalized by its value at zero and transported back to
canonical `su(N)` coordinates.  The additional `L⁻¹` in the printed
coefficient formula for `h(c)` is therefore already accounted for by the raw
represented-block derivative and must not be inserted again here.

This file names that literal physical operator.  It deliberately does not
identify its pivot right inverse with the flat insertion
`cmp96ConstraintPivotInsertion`.  The source right inverse `h` must instead
be obtained by inverting the pivot response of the operator below.

Honest scope: no invertibility, small-background estimate, or CMP109 fixed
point is proved here.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The literal `L Q̃` linear part of the represented nonlinear block
constraint, in canonical coarse physical Lie coordinates. -/
noncomputable def cmp109PhysicalLinearConstraint
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc) :
    CoarsePhysicalOneCochain d N' Nc :=
  WithLp.toLp 2 fun b =>
    cmp98AmbientToLieCoordCLM Nc
      (fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
          (cmp102PhysicalCochainToAmbientCLM A) *
        cmp98Eq119NonlinearBlockInverseAtZero U
          (0 : FinePhysicalOneCochain d L N' Nc) b)

@[simp] theorem cmp109PhysicalLinearConstraint_apply
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc)
    (b : PhysicalBond d N') :
    cmp109PhysicalLinearConstraint U A b =
      cmp98AmbientToLieCoordCLM Nc
        (fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
            (cmp102PhysicalCochainToAmbientCLM A) *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : FinePhysicalOneCochain d L N' Nc) b) := rfl

theorem cmp109PhysicalLinearConstraint_add
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A B : FinePhysicalOneCochain d L N' Nc) :
    cmp109PhysicalLinearConstraint U (A + B) =
      cmp109PhysicalLinearConstraint U A +
        cmp109PhysicalLinearConstraint U B := by
  apply PiLp.ext
  intro b
  simp only [cmp109PhysicalLinearConstraint_apply, PiLp.add_apply,
    map_add, add_mul]

theorem cmp109PhysicalLinearConstraint_smul
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ) (A : FinePhysicalOneCochain d L N' Nc) :
    cmp109PhysicalLinearConstraint U (a • A) =
      a • cmp109PhysicalLinearConstraint U A := by
  apply PiLp.ext
  intro b
  simp only [cmp109PhysicalLinearConstraint_apply, PiLp.smul_apply,
    map_smul, smul_mul_assoc]

/-- Bundled continuous-linear physical linear constraint.  Continuity follows
from finite dimensionality of the physical cochain spaces. -/
noncomputable def cmp109PhysicalLinearConstraintCLM
    (U : PhysicalGaugeBackground d (L * N') Nc) :
    FinePhysicalOneCochain d L N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := cmp109PhysicalLinearConstraint U
      map_add' := cmp109PhysicalLinearConstraint_add U
      map_smul' := cmp109PhysicalLinearConstraint_smul U }

@[simp] theorem cmp109PhysicalLinearConstraintCLM_apply
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (A : FinePhysicalOneCochain d L N' Nc) :
    cmp109PhysicalLinearConstraintCLM U A =
      cmp109PhysicalLinearConstraint U A := rfl

/-- The coarse pivot response obtained by inserting the existing flat sparse
pivot field and applying the literal physical linear constraint.  CMP109's
source `h` is obtained only after this response is inverted. -/
noncomputable def cmp109PhysicalPivotResponseCLM
    (U : PhysicalGaugeBackground d (L * N') Nc) :
    CoarsePhysicalOneCochain d N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc :=
  (cmp109PhysicalLinearConstraintCLM U).comp
    (cmp96ConstraintPivotInsertionCLM
      (d := d) (L := L) (N' := N') (Nc := Nc))

@[simp] theorem cmp109PhysicalPivotResponseCLM_apply
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (D : CoarsePhysicalOneCochain d N' Nc) :
    cmp109PhysicalPivotResponseCLM U D =
      cmp109PhysicalLinearConstraint U
        (cmp96ConstraintPivotInsertion (L := L) D) := rfl

end

end YangMills.RG
