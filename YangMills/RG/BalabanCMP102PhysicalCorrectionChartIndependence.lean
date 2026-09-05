/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalChartBudget

/-!
# Independence of the physical CMP102 correction from chart certificates

The logarithmic charts used to construct the physical correction carry
analytic certificates and a radius, but the value at the physical endpoint
is intrinsic.  Decoding either construction gives the same literal CMP98
equation-(122) remainder.  The exact retraction from ambient matrices to
canonical `su(N)` coordinates therefore removes the chart data completely.

This is the well-definedness lemma needed before the correction can be used
as the map in a fixed-point argument.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The bondwise physical correction is independent of the certified
logarithmic chart used to construct it. -/
theorem cmp102PhysicalNonlinearCorrectionField_apply_chart_independent
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (Chart₁ Chart₂ : CMP102PhysicalNonlinearFieldChart U A)
    (b : PhysicalBond d N') :
    cmp102PhysicalNonlinearCorrectionField U A Chart₁ b =
      cmp102PhysicalNonlinearCorrectionField U A Chart₂ b := by
  rw [← cmp98AmbientToLieCoordCLM_leftInverse
      (cmp102PhysicalNonlinearCorrectionField U A Chart₁ b),
    ← cmp98AmbientToLieCoordCLM_leftInverse
      (cmp102PhysicalNonlinearCorrectionField U A Chart₂ b)]
  congr 1
  rw [cmp102PhysicalNonlinearCorrectionField_toMatrix U A Chart₁ b,
    cmp102PhysicalNonlinearCorrectionField_toMatrix U A Chart₂ b]

/-- The assembled physical correction cochain is independent of all
bondwise chart certificates. -/
theorem cmp102PhysicalNonlinearCorrectionField_chart_independent
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (Chart₁ Chart₂ : CMP102PhysicalNonlinearFieldChart U A) :
    cmp102PhysicalNonlinearCorrectionField U A Chart₁ =
      cmp102PhysicalNonlinearCorrectionField U A Chart₂ := by
  unfold cmp102PhysicalNonlinearCorrectionField
  congr 1
  funext b
  exact cmp102PhysicalNonlinearCorrectionField_apply_chart_independent
    U A Chart₁ Chart₂ b

/-- In particular, two scalar source-budget packages for the same physical
field generate the same correction.  Their numerical radii and proof data
cannot affect the fixed-point map. -/
theorem cmp102PhysicalNonlinearCorrectionOfBudget_independent
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (B₁ B₂ : CMP102PhysicalNonlinearChartBudget U A) :
    cmp102PhysicalNonlinearCorrectionOfBudget U A B₁ =
      cmp102PhysicalNonlinearCorrectionOfBudget U A B₂ :=
  cmp102PhysicalNonlinearCorrectionField_chart_independent
    U A B₁.toFieldChart B₂.toFieldChart

end

end YangMills.RG
