/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98PhysicalSpecialUnitaryChart
import YangMills.RG.BalabanCMP99UbarSpecialUnitary

/-!
# The physical CMP98 logarithmic average is `su(N)`-valued

The ambient calculus for CMP98 differentiates matrix-valued logarithms.  On a
physical real line, however, every local four-contour is an element of
`SU(N)`.  Under the same near-identity and no-winding hypotheses used by the
source construction, its principal logarithm is skew-adjoint and traceless.

This file packages the literal finite average in `SuLie` and then transports
it to the fixed Euclidean coordinates `SUNLieCoord`.  The matrix represented
by the packaged coordinate is definitionally the already differentiated
`cmp98UbarLogAverage`; no projection or replacement is introduced.

The hypotheses are deliberately local to the logarithm domain.  No
contraction estimate or CMP102 fixed-point solution is claimed here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- On a physical line, the ambient CMP98 log average is exactly the
special-unitary exponent constructed from the literal four-contours. -/
theorem cmp98UbarLogAverage_physicalLine_eq_specialUnitaryExponent
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp98UbarLogAverage U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) =
      cmp99UbarSpecialUnitaryExponent
        (blockOf M N' b.1)
        (fun _ => ((M : ℝ) ^ d)⁻¹)
        (fun x => cmp98PhysicalUbarRelativeSUN U A b x t) := by
  unfold cmp98UbarLogAverage cmp99UbarSpecialUnitaryExponent
    cmp99UbarUnitaryExponent cmp99UbarExponent
  have hlogs :
      (∑ x ∈ blockOf M N' b.1,
        nearLog (cmp98UbarAmbientDeviationMatrix U b x
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)))) =
      ∑ x ∈ blockOf M N' b.1,
        nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [cmp98UbarAmbientDeviationMatrix_line_eq_relativeSUN_sub_one]
  calc
    ((M : ℝ) ^ d)⁻¹ •
        ∑ x ∈ blockOf M N' b.1,
          nearLog (cmp98UbarAmbientDeviationMatrix U b x
            (t • physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent A))) =
      ((M : ℝ) ^ d)⁻¹ •
        ∑ x ∈ blockOf M N' b.1,
          nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1) := congrArg _ hlogs
    _ = ∑ x ∈ blockOf M N' b.1, ((M : ℝ) ^ d)⁻¹ •
        nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1) :=
      Finset.smul_sum

/-- The literal physical logarithmic block average, with its genuine
`su(N)` codomain restored. -/
noncomputable def cmp98PhysicalUbarLogAverageSuLie
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    SuLie Nc := by
  let s := blockOf M N' b.1
  let w : FinBox d (M * N') → ℝ := fun _ => ((M : ℝ) ^ d)⁻¹
  let D : FinBox d (M * N') → SUN Nc :=
    fun x => cmp98PhysicalUbarRelativeSUN U A b x t
  let Z := cmp99UbarSpecialUnitaryExponent s w D
  have hskew :
      Z ∈ skewAdjoint (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    cmp99UbarSpecialUnitaryExponent_mem_skewAdjoint s w D hnear
  have htrace : Matrix.trace Z = 0 :=
    trace_cmp99UbarSpecialUnitaryExponent_eq_zero
      s w D hnear hnoWinding
  refine ⟨cmp98UbarLogAverage U b
      (t • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A)), ?_⟩
  rw [mem_suMatrixSubmodule_iff]
  rw [cmp98UbarLogAverage_physicalLine_eq_specialUnitaryExponent]
  exact ⟨(skewAdjoint.mem_iff.mp hskew), htrace⟩

@[simp] theorem cmp98PhysicalUbarLogAverageSuLie_toMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    (cmp98PhysicalUbarLogAverageSuLie U A b t hnear hnoWinding).toMatrix =
      cmp98UbarLogAverage U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) := by
  rfl

/-- The same literal logarithmic average in the canonical real coordinates
used by the CMP102 correction map. -/
noncomputable def cmp98PhysicalUbarLogAverageLieCoord
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    SUNLieCoord Nc :=
  suLieCoordIso Nc
    (cmp98PhysicalUbarLogAverageSuLie
      U A b t hnear hnoWinding)

/-- Decoding the physical coordinate recovers the exact ambient matrix
already used by the CMP98 calculus. -/
theorem cmp98PhysicalUbarLogAverageLieCoord_toMatrix
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ)
    (hnear : ∀ x ∈ blockOf M N' b.1,
      ‖(cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ < 1)
    (hnoWinding : ∀ x ∈ blockOf M N' b.1, (Nc : ℝ) *
      ‖nearLog ((cmp98PhysicalUbarRelativeSUN U A b x t :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ < 2 * Real.pi) :
    ((suLieCoordIso Nc).symm
      (cmp98PhysicalUbarLogAverageLieCoord
        U A b t hnear hnoWinding)).toMatrix =
      cmp98UbarLogAverage U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) := by
  rw [cmp98PhysicalUbarLogAverageLieCoord]
  rw [(suLieCoordIso Nc).symm_apply_apply]
  rfl

end

end YangMills.RG
