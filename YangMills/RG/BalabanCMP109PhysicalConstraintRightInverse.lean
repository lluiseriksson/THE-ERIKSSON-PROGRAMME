/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109PhysicalLinearConstraint
import YangMills.RG.BalabanCMP99PatchedParametrixNeumann

/-!
# A source-facing CMP109 constraint right-inverse candidate

Let `Qlin_U = L Q̃_U` be the literal raw linearization of the represented
nonlinear block constraint and let `P₀` be the sparse flat pivot insertion.
The coarse pivot response is

`K_U = Qlin_U ∘ P₀`.

When its physical defect `K_U - I` is a contraction, a physical right inverse
is constructed, rather than postulated, by

`h_U = P₀ ∘ (I + (K_U - I))⁻¹`

with the inverse given by the convergent Neumann series.  This file proves the
exact right-inverse identity `Qlin_U ∘ h_U = I`.  It becomes the literal
source `h`, for which the value at `b₀(c)` depends only on the coarse value at
`c`, only after block-diagonality of `K_U⁻¹` is proved.

Honest scope: neither the contraction estimate for `K_U - I` nor the
block-diagonal/locality theorem is proved here.  Both must be discharged from
the small-background geometry of the literal physical block derivative; they
are not admissible terminal hypotheses.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- Difference between the physical pivot response and the identity. -/
noncomputable def cmp109PhysicalPivotDefectCLM
    (U : PhysicalGaugeBackground d (L * N') Nc) :
    CoarsePhysicalOneCochain d N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc :=
  cmp109PhysicalPivotResponseCLM U -
    ContinuousLinearMap.id ℝ (CoarsePhysicalOneCochain d N' Nc)

/-- The physical pivot response is exactly identity plus its named defect. -/
theorem cmp109PhysicalPivotResponseCLM_eq_id_add_defect
    (U : PhysicalGaugeBackground d (L * N') Nc) :
    cmp109PhysicalPivotResponseCLM U =
      ContinuousLinearMap.id ℝ (CoarsePhysicalOneCochain d N' Nc) +
        cmp109PhysicalPivotDefectCLM U := by
  unfold cmp109PhysicalPivotDefectCLM
  abel

/-- Neumann inverse of the literal physical pivot response. -/
noncomputable def cmp109PhysicalPivotInverseCLM
    (U : PhysicalGaugeBackground d (L * N') Nc) :
    CoarsePhysicalOneCochain d N' Nc →L[ℝ]
      CoarsePhysicalOneCochain d N' Nc :=
  cmp99PatchedDefectNeumannInverse (cmp109PhysicalPivotDefectCLM U)

/-- The physical pivot response composed with its constructed inverse is the
identity whenever the visible defect is a contraction. -/
theorem cmp109PhysicalPivotResponse_comp_inverse
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hsmall : ‖cmp109PhysicalPivotDefectCLM U‖ < 1) :
    (cmp109PhysicalPivotResponseCLM U).comp
        (cmp109PhysicalPivotInverseCLM U) =
      ContinuousLinearMap.id ℝ
        (CoarsePhysicalOneCochain d N' Nc) := by
  rw [cmp109PhysicalPivotResponseCLM_eq_id_add_defect]
  exact one_add_comp_cmp99PatchedDefectNeumannInverse
    (cmp109PhysicalPivotDefectCLM U) hsmall

/-- The inverse identity in the opposite order. -/
theorem cmp109PhysicalPivotInverse_comp_response
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hsmall : ‖cmp109PhysicalPivotDefectCLM U‖ < 1) :
    (cmp109PhysicalPivotInverseCLM U).comp
        (cmp109PhysicalPivotResponseCLM U) =
      ContinuousLinearMap.id ℝ
        (CoarsePhysicalOneCochain d N' Nc) := by
  rw [cmp109PhysicalPivotResponseCLM_eq_id_add_defect]
  exact cmp99PatchedDefectNeumannInverse_comp_one_add
    (cmp109PhysicalPivotDefectCLM U) hsmall

/-- A physical constraint right inverse: first solve the physical pivot
response on the coarse field, then insert the resulting sparse pivot field.
Its image is supported on the set of pivot bonds, but source-local dependence
on the matching coarse bond still requires block-diagonality of the pivot
response. -/
noncomputable def cmp109PhysicalConstraintRightInverseCLM
    (U : PhysicalGaugeBackground d (L * N') Nc) :
    CoarsePhysicalOneCochain d N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  (cmp96ConstraintPivotInsertionCLM
      (d := d) (L := L) (N' := N') (Nc := Nc)).comp
    (cmp109PhysicalPivotInverseCLM U)

@[simp] theorem cmp109PhysicalConstraintRightInverseCLM_apply
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (D : CoarsePhysicalOneCochain d N' Nc) :
    cmp109PhysicalConstraintRightInverseCLM U D =
      cmp96ConstraintPivotInsertion (L := L)
        (cmp109PhysicalPivotInverseCLM U D) := rfl

/-- Exact source identity `Qlin_U h_U = I`. -/
theorem cmp109PhysicalLinearConstraint_comp_rightInverse
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hsmall : ‖cmp109PhysicalPivotDefectCLM U‖ < 1) :
    (cmp109PhysicalLinearConstraintCLM U).comp
        (cmp109PhysicalConstraintRightInverseCLM U) =
      ContinuousLinearMap.id ℝ
        (CoarsePhysicalOneCochain d N' Nc) := by
  rw [cmp109PhysicalConstraintRightInverseCLM,
    ← ContinuousLinearMap.comp_assoc]
  change (cmp109PhysicalPivotResponseCLM U).comp
      (cmp109PhysicalPivotInverseCLM U) =
    ContinuousLinearMap.id ℝ
      (CoarsePhysicalOneCochain d N' Nc)
  exact cmp109PhysicalPivotResponse_comp_inverse U hsmall

/-- Pointwise form of the physical right-inverse identity. -/
theorem cmp109PhysicalLinearConstraint_rightInverse_apply
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (hsmall : ‖cmp109PhysicalPivotDefectCLM U‖ < 1)
    (D : CoarsePhysicalOneCochain d N' Nc) :
    cmp109PhysicalLinearConstraintCLM U
        (cmp109PhysicalConstraintRightInverseCLM U D) = D := by
  have h := congrArg
    (fun T : CoarsePhysicalOneCochain d N' Nc →L[ℝ]
        CoarsePhysicalOneCochain d N' Nc => T D)
    (cmp109PhysicalLinearConstraint_comp_rightInverse U hsmall)
  simpa using h

end

end YangMills.RG
