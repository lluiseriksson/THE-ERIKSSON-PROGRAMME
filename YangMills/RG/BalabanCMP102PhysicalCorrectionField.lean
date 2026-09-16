/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98PhysicalRightVariation
import YangMills.RG.BalabanCMP98Eq123LogBound

/-!
# The physical CMP102 correction field

The preceding module constructs the nonlinear correction along each physical
ray.  This file evaluates that ray at its physical endpoint and assembles the
bondwise values into a coarse one-cochain.

The chart data below are deliberately field-specific.  They certify that the
literal logarithms used by CMP98 exist along the unit segment for the supplied
field; they are not a contraction estimate and are not used to postulate the
value of the correction.  The resulting cochain is defined pointwise from the
special-unitary construction, and decoding each coordinate gives exactly the
ambient logarithmic remainder of CMP98 equation (122).

Honest scope: this is the source correction `C(A)` at a certified field `A`.
It does not yet prove that all fields in a norm ball admit the chart, that
`C` is Lipschitz on such a ball, or that `D(A) = C(A - H D(A))` has a fixed
point.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- A simultaneous physical logarithmic chart for every coarse bond, with
the endpoint `t = 1` strictly inside every certified interval. -/
structure CMP102PhysicalNonlinearFieldChart
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) where
  chart : ∀ b : PhysicalBond d N',
    CMP98PhysicalNonlinearLocalChart U A b
  one_lt_radius : ∀ b : PhysicalBond d N', 1 < (chart b).radius

namespace CMP102PhysicalNonlinearFieldChart

variable
    {U : PhysicalGaugeBackground d (M * N') Nc}
    {A : PhysicalGaugeOneCochain d (M * N') Nc}
    (Chart : CMP102PhysicalNonlinearFieldChart U A)

/-- The unit endpoint belongs to every bondwise logarithmic chart. -/
theorem one_mem (b : PhysicalBond d N') :
    |(1 : ℝ)| < (Chart.chart b).radius := by
  simpa using Chart.one_lt_radius b

end CMP102PhysicalNonlinearFieldChart

/-- The physical CMP102 correction assembled as a coarse one-cochain. -/
noncomputable def cmp102PhysicalNonlinearCorrectionField
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (Chart : CMP102PhysicalNonlinearFieldChart U A) :
    CoarsePhysicalOneCochain d N' Nc :=
  WithLp.toLp 2 fun b : PhysicalBond d N' =>
    cmp102PhysicalNonlinearCorrectionRay U A b (Chart.chart b) 1

@[simp] theorem cmp102PhysicalNonlinearCorrectionField_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (Chart : CMP102PhysicalNonlinearFieldChart U A)
    (b : PhysicalBond d N') :
    cmp102PhysicalNonlinearCorrectionField U A Chart b =
      cmp102PhysicalNonlinearCorrectionRay U A b (Chart.chart b) 1 := by
  rfl

/-- Pointwise source fidelity: decoding the physical correction cochain gives
the literal CMP98 equation (122) remainder at the unit endpoint. -/
theorem cmp102PhysicalNonlinearCorrectionField_toMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (Chart : CMP102PhysicalNonlinearFieldChart U A)
    (b : PhysicalBond d N') :
    cmp98LieCoordToAmbientCLM Nc
        (cmp102PhysicalNonlinearCorrectionField U A Chart b) =
      cmp98Eq122NonlinearLogRemainder U A b 1 := by
  rw [cmp102PhysicalNonlinearCorrectionField_apply]
  exact cmp102PhysicalNonlinearCorrectionRay_toMatrix_of_abs_lt
    U A b (Chart.chart b) (Chart.one_mem b)

/-- The operator norm of the decoded physical correction is exactly the
operator norm of the literal CMP98 remainder.  This deliberately does not
identify the Euclidean coordinate norm with the matrix operator norm. -/
theorem norm_cmp102PhysicalNonlinearCorrectionField_toMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (Chart : CMP102PhysicalNonlinearFieldChart U A)
    (b : PhysicalBond d N') :
    ‖cmp98LieCoordToAmbientCLM Nc
        (cmp102PhysicalNonlinearCorrectionField U A Chart b)‖ =
      ‖cmp98Eq122NonlinearLogRemainder U A b 1‖ := by
  rw [cmp102PhysicalNonlinearCorrectionField_toMatrix U A Chart b]

set_option maxHeartbeats 3000000 in
/-- The existing source-explicit CMP98 remainder budget applies directly to
each coordinate of the physical correction field. -/
theorem norm_cmp102PhysicalNonlinearCorrectionField_toMatrix_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (Chart : CMP102PhysicalNonlinearFieldChart U A)
    (b : PhysicalBond d N') (r : ℝ)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hr : 1 / 3 + cmp98SourceContourDisplacementBudget A 1 ≤ r)
    (hr1 : r < 1)
    (hdev1 : cmp98SourcePhysicalBlockDisplacementBudget A 1 r < 1) :
    let R := cmp98SourceLogAverageRadius r
    let D := nearLogDerivativeBudget r *
      cmp98SourceContourDisplacementBudget A 1
    let Q := nearLogSecondDerivativeBudget r *
          cmp98SourceContourDisplacementBudget A 1 ^ 2 +
        nearLogDerivativeBudget r *
          cmp98SourceContourQuadraticBudget A 1
    let QE := expSecondDerivativeBudget R * D ^ 2 +
      expDerivativeBudget R * Q
    let B := cmp98SourcePhysicalBlockDisplacementBudget A 1 r
    ‖cmp98LieCoordToAmbientCLM Nc
        (cmp102PhysicalNonlinearCorrectionField U A Chart b)‖ ≤
      B ^ 2 / (1 - B) +
        (QE + cmp98SourceOuterExpNormBudget r *
            cmp98SourceCoarseContourQuadraticBudget A 1 +
          cmp98SourceOuterExpDisplacementBudget A 1 r *
            cmp98SourceCoarseContourDisplacementBudget A 1) *
          cmp98SourceOuterExpNormBudget r := by
  rw [norm_cmp102PhysicalNonlinearCorrectionField_toMatrix U A Chart b]
  apply norm_cmp98Eq122NonlinearLogRemainder_le_sourceBudget
    U A b 1 r hbase
  · simpa using hsmall
  · exact hr
  · exact hr1
  · exact hdev1

end

end YangMills.RG
