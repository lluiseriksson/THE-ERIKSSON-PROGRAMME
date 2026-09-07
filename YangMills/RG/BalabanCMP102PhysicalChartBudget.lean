/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalCorrectionNorm
import YangMills.RG.NearLogDeviationBudget

/-!
# Source-explicit production of the physical CMP102 logarithmic chart

The physical correction field was initially packaged with a bondwise chart
certificate.  This module produces that certificate from the scalar budgets
already proved in the CMP98 source chain.

There are two genuinely different no-winding balls:

* the local four-contour deviations entering the block logarithmic average;
* the normalized nonlinear block deviation entering the final logarithm.

The first is controlled by the background `1/3` margin plus the explicit
contour displacement.  The second is controlled by the source-explicit
physical block displacement budget.  Thus none of the four analytic chart
properties is supplied directly by the caller.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Scalar source data sufficient to produce every logarithmic chart used by
the physical CMP102 correction at the supplied field. -/
structure CMP102PhysicalNonlinearChartBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) where
  radius : ℝ
  one_lt_radius : 1 < radius
  localNoWinding : MatrixNearLogNoWindingBudget Nc
  relativeNoWinding : MatrixNearLogNoWindingBudget Nc
  base : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
    ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3
  small : ∀ t, |t| < radius →
    |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2
  localRadius : ∀ t, |t| < radius →
    1 / 3 + cmp98SourceContourDisplacementBudget A t ≤
      localNoWinding.δ
  relativeRadius : ∀ t, |t| < radius →
    cmp98SourcePhysicalBlockDisplacementBudget
        A t localNoWinding.δ ≤ relativeNoWinding.δ

namespace CMP102PhysicalNonlinearChartBudget

variable
    {U : PhysicalGaugeBackground d (M * N') Nc}
    {A : PhysicalGaugeOneCochain d (M * N') Nc}
    (B : CMP102PhysicalNonlinearChartBudget U A)

/-- Zero belongs to the common source chart. -/
theorem zero_mem : |(0 : ℝ)| < B.radius := by
  simpa using lt_trans zero_lt_one B.one_lt_radius

/-- The source budgets control one local four-contour deviation. -/
theorem local_deviation_le
    (b : PhysicalBond d N') (t : ℝ) (ht : |t| < B.radius)
    (x : FinBox d (M * N')) (hx : x ∈ blockOf M N' b.1) :
    ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      B.localNoWinding.δ := by
  rw [← cmp98UbarAmbientDeviationMatrix_line_eq_relativeSUN_sub_one]
  let Dt := cmp98UbarAmbientDeviationMatrix U b x
    (t • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A))
  let D0 := cmp98UbarAmbientDeviationMatrix U b x 0
  have hdisp :
      ‖Dt - D0‖ ≤ cmp98SourceContourDisplacementBudget A t := by
    simpa [Dt, D0, cmp98SourceContourDisplacementBudget] using
      norm_cmp98UbarAmbientDeviationMatrix_physicalLine_sub_zero_le
        U A b x hx t (B.small t ht)
  have htri : ‖Dt‖ ≤ ‖Dt - D0‖ + ‖D0‖ := by
    simpa only [sub_add_cancel] using norm_add_le (Dt - D0) D0
  exact htri.trans
    ((add_le_add hdisp (B.base b x hx)).trans (by
      linarith [B.localRadius t ht]))

/-- The local physical four-contour lies in the Mercator unit ball. -/
theorem near
    (b : PhysicalBond d N') (t : ℝ) (ht : |t| < B.radius) :
    ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1 := by
  intro x hx
  exact B.localNoWinding.nearIdentity _
    (B.local_deviation_le b t ht x hx)

/-- The local physical four-contour cannot cross a determinant winding. -/
theorem noWinding
    (b : PhysicalBond d N') (t : ℝ) (ht : |t| < B.radius) :
    ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi := by
  intro x hx
  exact B.localNoWinding.nearLog_noWinding _
    (B.local_deviation_le b t ht x hx)

/-- The source budgets control the normalized nonlinear block deviation. -/
theorem relative_deviation_le
    (b : PhysicalBond d N') (t : ℝ) (ht : |t| < B.radius) :
    ‖(cmp98PhysicalNonlinearRelativeSUN U A b t
        (B.near b t ht) (B.noWinding b t ht)
        (B.near b 0 B.zero_mem)
        (B.noWinding b 0 B.zero_mem) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      B.relativeNoWinding.δ := by
  rw [← cmp98Eq119NonlinearRelativeDeviation_eq_relativeSUN_sub_one]
  exact
    (norm_cmp98Eq119NonlinearRelativeDeviation_le_sourceBudget
      U A b t B.localNoWinding.δ (B.base b) (B.small t ht)
      (B.localRadius t ht) B.localNoWinding.δ_lt_one).trans
        (B.relativeRadius t ht)

/-- The normalized nonlinear block lies in its Mercator unit ball. -/
theorem relativeNear
    (b : PhysicalBond d N') (t : ℝ) (ht : |t| < B.radius) :
    ‖(cmp98PhysicalNonlinearRelativeSUN U A b t
        (B.near b t ht) (B.noWinding b t ht)
        (B.near b 0 B.zero_mem)
        (B.noWinding b 0 B.zero_mem) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1 :=
  B.relativeNoWinding.nearIdentity _
    (B.relative_deviation_le b t ht)

/-- The normalized nonlinear block cannot cross a determinant winding. -/
theorem relativeNoWinding'
    (b : PhysicalBond d N') (t : ℝ) (ht : |t| < B.radius) :
    (Nc : ℝ) *
      ‖nearLog
        ((cmp98PhysicalNonlinearRelativeSUN U A b t
          (B.near b t ht) (B.noWinding b t ht)
          (B.near b 0 B.zero_mem)
          (B.noWinding b 0 B.zero_mem) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi :=
  B.relativeNoWinding.nearLog_noWinding _
    (B.relative_deviation_le b t ht)

/-- A scalar source budget produces the complete bondwise physical chart. -/
noncomputable def toLocalChart (b : PhysicalBond d N') :
    CMP98PhysicalNonlinearLocalChart U A b where
  radius := B.radius
  radius_pos := lt_trans zero_lt_one B.one_lt_radius
  near := B.near b
  noWinding := B.noWinding b
  relativeNear := B.relativeNear b
  relativeNoWinding := B.relativeNoWinding' b

/-- A scalar source budget produces the simultaneous chart on the entire
coarse correction field. -/
noncomputable def toFieldChart :
    CMP102PhysicalNonlinearFieldChart U A where
  chart := B.toLocalChart
  one_lt_radius := fun _ => B.one_lt_radius

end CMP102PhysicalNonlinearChartBudget

/-- The physical correction with all chart data generated from scalar source
budgets. -/
noncomputable def cmp102PhysicalNonlinearCorrectionOfBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (B : CMP102PhysicalNonlinearChartBudget U A) :
    CoarsePhysicalOneCochain d N' Nc :=
  cmp102PhysicalNonlinearCorrectionField U A B.toFieldChart

@[simp] theorem cmp102PhysicalNonlinearCorrectionOfBudget_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (B : CMP102PhysicalNonlinearChartBudget U A)
    (b : PhysicalBond d N') :
    cmp102PhysicalNonlinearCorrectionOfBudget U A B b =
      cmp102PhysicalNonlinearCorrectionRay U A b
        (B.toLocalChart b) 1 := by
  rfl

/-- Decoding the budget-generated correction still gives exactly the literal
CMP98 equation (122) remainder. -/
theorem cmp102PhysicalNonlinearCorrectionOfBudget_toMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (B : CMP102PhysicalNonlinearChartBudget U A)
    (b : PhysicalBond d N') :
    cmp98LieCoordToAmbientCLM Nc
        (cmp102PhysicalNonlinearCorrectionOfBudget U A B b) =
      cmp98Eq122NonlinearLogRemainder U A b 1 :=
  cmp102PhysicalNonlinearCorrectionField_toMatrix
    U A B.toFieldChart b

end

end YangMills.RG
