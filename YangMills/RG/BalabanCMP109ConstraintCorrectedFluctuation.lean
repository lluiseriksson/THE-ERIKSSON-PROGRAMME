/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109ConstraintCorrectionFixedPoint

/-!
# The literal corrected fluctuation in CMP109 equation (1.3.2)

With `C` the physical constraint-elimination projection and `h` its sparse
right inverse, CMP109 uses

`B' = g_k C B - h D_tilde(g_k C B)`.

This file installs that formula literally.  It proves first that its flat
block constraint is `-D`; when `D` is the nonlinear correction evaluated at
the same field, the complete linear-plus-nonlinear constraint vanishes
exactly.  The terminal theorem obtains such a `D` from the Banach producer of
`BalabanCMP109ConstraintCorrectionFixedPoint`.

No group-valued minimal-orbit map `U_k`, localized activity, residual
`V''_k`, or estimate (1.36) is asserted here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- The constrained linear part `g_k C B` of the CMP109 fluctuation. -/
noncomputable def cmp109ConstrainedLinearFluctuation
    (gk : ℝ) (B : FinePhysicalOneCochain d L N' Nc) :
    FinePhysicalOneCochain d L N' Nc :=
  gk • cmp96ConstraintEliminationCLM (L := L) B

/-- Literal CMP109 corrected fluctuation `g_k C B - h D`. -/
noncomputable def cmp109ConstraintCorrectedFluctuation
    (gk : ℝ) (B : FinePhysicalOneCochain d L N' Nc)
    (D : CoarsePhysicalOneCochain d N' Nc) :
    FinePhysicalOneCochain d L N' Nc :=
  cmp109ConstrainedLinearFluctuation (L := L) gk B -
    cmp96ConstraintPivotInsertion (L := L) D

/-- The linear part lies exactly in the kernel of the flat block
constraint. -/
theorem flatBlockConstraint_cmp109ConstrainedLinearFluctuation
    (gk : ℝ) (B : FinePhysicalOneCochain d L N' Nc) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (cmp109ConstrainedLinearFluctuation (L := L) gk B) = 0 := by
  unfold cmp109ConstrainedLinearFluctuation
  rw [map_smul, flatBlockConstraint_cmp96ConstraintEliminationCLM,
    smul_zero]

/-- Before the nonlinear correction is added, the corrected fluctuation has
flat block constraint exactly `-D`. -/
theorem flatBlockConstraint_cmp109ConstraintCorrectedFluctuation
    (gk : ℝ) (B : FinePhysicalOneCochain d L N' Nc)
    (D : CoarsePhysicalOneCochain d N' Nc) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (cmp109ConstraintCorrectedFluctuation (L := L) gk B D) = -D := by
  unfold cmp109ConstraintCorrectedFluctuation
  rw [map_sub,
    flatBlockConstraint_cmp109ConstrainedLinearFluctuation]
  have hright :
      flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
          (cmp96ConstraintPivotInsertion (L := L) D) = D := by
    change
      (((flatBlockConstraintQCLM (d := d) (Nc := Nc) L N').comp
        (cmp96ConstraintPivotInsertionCLM
          (d := d) (L := L) (N' := N') (Nc := Nc))) D) = D
    rw [flatBlockConstraint_comp_pivotInsertionCLM]
    rfl
  rw [hright, zero_sub]

/-- The literal fixed-point equation cancels the complete physical
linear-plus-nonlinear block constraint. -/
theorem cmp109ConstraintCorrectedFluctuation_fullConstraint
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain d L N' Nc)
    (D : CoarsePhysicalOneCochain d N' Nc)
    (Chart : CMP102PhysicalNonlinearChartBudget U
      (cmp109ConstraintCorrectedFluctuation (L := L) gk B D))
    (hD :
      cmp102PhysicalNonlinearCorrectionOfBudget U
        (cmp109ConstraintCorrectedFluctuation (L := L) gk B D) Chart = D) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
          (cmp109ConstraintCorrectedFluctuation (L := L) gk B D) +
        cmp102PhysicalNonlinearCorrectionOfBudget U
          (cmp109ConstraintCorrectedFluctuation (L := L) gk B D) Chart =
      0 := by
  rw [flatBlockConstraint_cmp109ConstraintCorrectedFluctuation, hD]
  exact neg_add_cancel D

/-- Banach produces a literal corrected fluctuation satisfying the complete
physical constraint.  No correction field or fixed-point equation is passed
to this theorem. -/
theorem
    CMP109ConstraintCorrectionBallData.exists_correctedFluctuation_fullConstraint
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain d L N' Nc)
    (ρ r s : ℝ)
    (Data : CMP109ConstraintCorrectionBallData U
      (cmp109ConstrainedLinearFluctuation (L := L) gk B) ρ r s)
    (hcontract : Data.contractionRate < 1) :
    ∃ (D : CoarsePhysicalOneCochain d N' Nc)
      (Chart : CMP102PhysicalNonlinearChartBudget U
        (cmp109ConstraintCorrectedFluctuation (L := L) gk B D)),
      cmp102PhysicalCorrectionSupNorm D ≤ ρ ∧
        flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
              (cmp109ConstraintCorrectedFluctuation (L := L) gk B D) +
            cmp102PhysicalNonlinearCorrectionOfBudget U
              (cmp109ConstraintCorrectedFluctuation (L := L) gk B D) Chart =
          0 := by
  rcases Data.exists_constraintCorrection_physicalEquation hcontract with
    ⟨Dsup, hDsup, hfix⟩
  let D : CoarsePhysicalOneCochain d N' Nc :=
    physicalGaugeOneCochainSupEquiv.symm Dsup
  have hDnorm : cmp102PhysicalCorrectionSupNorm D ≤ ρ := by
    rw [← norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm]
    simpa [D] using hDsup
  let Chart := Data.chartBudget Dsup hDsup
  have hfield :
      cmp109ConstrainedLinearFluctuation (L := L) gk B -
          cmp96ConstraintPivotInsertion (L := L)
            (physicalGaugeOneCochainSupEquiv.symm Dsup) =
        cmp109ConstraintCorrectedFluctuation (L := L) gk B D := rfl
  have hfixPhysical :
      cmp102PhysicalNonlinearCorrectionOfBudget U
          (cmp109ConstraintCorrectedFluctuation (L := L) gk B D) Chart =
        D := by
    apply physicalGaugeOneCochainSupEquiv.injective
    simpa [D, Chart, hfield] using hfix
  exact ⟨D, Chart, hDnorm,
    cmp109ConstraintCorrectedFluctuation_fullConstraint
      U gk B D Chart hfixPhysical⟩

end

end YangMills.RG
