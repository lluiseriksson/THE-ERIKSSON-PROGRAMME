/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98Eq122NonlinearLogJet
import YangMills.RG.NearLogFDeriv

/-!
# The exact quadratic frontier in CMP98 (123)

The logarithmic remainder in (122) has two mathematically distinct sources:
the quadratic Mercator correction and the nonlinear remainder of the physical
represented block before taking its logarithm.  This file separates them
exactly.

The first source is discharged unconditionally: differentiability of the
physical deviation gives `D(t) = O(t)`, while the previously proved Mercator
estimate `nearLog D - D = O(‖D‖²)` gives a composed `O(t²)` bound.  Consequently
the full estimate (123) is equivalent to the quadratic estimate for the
literal physical block remainder.  No constant or second-derivative bound is
introduced as a renamed hypothesis.
-/

namespace YangMills.RG

open YangMills Matrix Asymptotics
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98Eq123QuadraticFrontierMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The physical nonlinear remainder before applying the local logarithm. -/
def cmp98Eq123PhysicalBlockRemainder
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98Eq119NonlinearRelativeDeviation U A b t -
    t • cmp98Eq119NonlinearRightVariation U A b

/-- Exact separation of the logarithmic remainder into the Mercator
correction and the nonlinear physical-block remainder. -/
theorem cmp98Eq122NonlinearLogRemainder_eq_nearLogCorrection_add_physicalRemainder
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98Eq122NonlinearLogRemainder U A b t =
      (nearLog (cmp98Eq119NonlinearRelativeDeviation U A b t) -
          cmp98Eq119NonlinearRelativeDeviation U A b t) +
        cmp98Eq123PhysicalBlockRemainder U A b t := by
  unfold cmp98Eq122NonlinearLogRemainder cmp98Eq119NonlinearLogCoordinate
    cmp98Eq123PhysicalBlockRemainder
  abel

/-- The exact relative deviation is linearly bounded at the background. -/
theorem cmp98Eq119NonlinearRelativeDeviation_isBigO_id
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp98Eq119NonlinearRelativeDeviation U A b =O[nhds 0]
      (fun t : ℝ => t) := by
  have h :=
    (hasDerivAt_cmp98Eq119NonlinearRelativeDeviation U A b hsmall).hasFDerivAt.isBigO_sub
  simpa using h

/-- The Mercator part of (123) is already quadratically bounded.  This uses
only the physical first derivative and the sharp local logarithm remainder. -/
theorem cmp98Eq122NearLogCorrection_isBigO_sq
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    (fun t : ℝ =>
      nearLog (cmp98Eq119NonlinearRelativeDeviation U A b t) -
        cmp98Eq119NonlinearRelativeDeviation U A b t) =O[nhds 0]
      (fun t : ℝ => t ^ 2) := by
  have hdevDeriv :=
    hasDerivAt_cmp98Eq119NonlinearRelativeDeviation U A b hsmall
  have hdevTendsto :
      Filter.Tendsto (cmp98Eq119NonlinearRelativeDeviation U A b)
        (nhds 0) (nhds 0) := by
    simpa using hdevDeriv.continuousAt.tendsto
  have hlog :=
    (nearLog_sub_self_isBigO_norm_sq
      (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)).comp_tendsto hdevTendsto
  have hdev :=
    cmp98Eq119NonlinearRelativeDeviation_isBigO_id U A b hsmall
  exact hlog.trans (hdev.norm_left.pow 2)

/-- Exact analytic frontier of (123): the full logarithmic remainder is
quadratic if and only if the literal represented block has a quadratic
remainder before applying `nearLog`. -/
theorem cmp98Eq122NonlinearLogRemainder_isBigO_sq_iff_physicalBlockRemainder
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp98Eq122NonlinearLogRemainder U A b =O[nhds 0]
        (fun t : ℝ => t ^ 2) ↔
      cmp98Eq123PhysicalBlockRemainder U A b =O[nhds 0]
        (fun t : ℝ => t ^ 2) := by
  have hlog := cmp98Eq122NearLogCorrection_isBigO_sq U A b hsmall
  have hdecomp :
      cmp98Eq122NonlinearLogRemainder U A b =
        (fun t : ℝ =>
          (nearLog (cmp98Eq119NonlinearRelativeDeviation U A b t) -
              cmp98Eq119NonlinearRelativeDeviation U A b t) +
            cmp98Eq123PhysicalBlockRemainder U A b t) := by
    funext t
    exact
      cmp98Eq122NonlinearLogRemainder_eq_nearLogCorrection_add_physicalRemainder
        U A b t
  rw [hdecomp]
  exact hlog.add_iff_right

end

end YangMills.RG
