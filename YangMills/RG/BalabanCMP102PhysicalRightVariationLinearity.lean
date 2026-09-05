/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalTwoFieldRelativeLog

/-!
# Exact field-linearity of the physical CMP98 right variation

The term subtracted in equation (122) is the derivative at the background
of one fixed ambient represented-block map.  This module exposes that map,
identifies its Fréchet derivative with the literal physical right
variation, and deduces exact subtraction-linearity in the tangent field.

This is an algebraic checkpoint, not yet the source-sup-norm estimate for
that linear term.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The fixed ambient represented-block map whose physical radial
restriction is the nonlinear block curve. -/
def cmp102AmbientNonlinearBlock
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  cmp98UbarExpAverage U b Z *
    cmp98AmbientWilsonLineMatrix U Z
      (cmp98SourceCoarseBondPath (Nc := Nc) b)

/-- Restricting the fixed ambient map to a physical line gives the literal
CMP98 nonlinear block curve. -/
theorem cmp102AmbientNonlinearBlock_physicalLine_eq
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (t : ℝ) :
    cmp102AmbientNonlinearBlock U b
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) =
      cmp98Eq119NonlinearBlockCurve U A b t := by
  unfold cmp102AmbientNonlinearBlock cmp98Eq119NonlinearBlockCurve
  rw [cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve]

/-- The derivative of the fixed ambient block, evaluated on a physical
field, is exactly the derivative of the literal physical block curve. -/
theorem fderiv_cmp102AmbientNonlinearBlock_zero_apply_physical
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) =
      deriv (cmp98Eq119NonlinearBlockCurve U A b) 0 := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  let V : PhysicalAmbientMatrixTangent d (M * N') Nc :=
    physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A)
  have houter := hasFDerivAt_cmp98UbarExpAverage U b hsmall
  have hcontour :
      HasFDerivAt
        (fun Z => cmp98AmbientWilsonLineMatrix U Z
          (cmp98SourceCoarseBondPath (Nc := Nc) b))
        (fderiv ℝ
          (fun Z => cmp98AmbientWilsonLineMatrix U Z
            (cmp98SourceCoarseBondPath (Nc := Nc) b)) 0) 0 :=
    (analyticAt_cmp98AmbientWilsonLineMatrix U 0
      (cmp98SourceCoarseBondPath (Nc := Nc) b)).differentiableAt.hasFDerivAt
  have hambient :
      HasFDerivAt (cmp102AmbientNonlinearBlock U b)
        (fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0) 0 := by
    have hdiff :
        DifferentiableAt ℝ (cmp102AmbientNonlinearBlock U b) 0 := by
      unfold cmp102AmbientNonlinearBlock
      exact houter.differentiableAt.mul hcontour.differentiableAt
    exact hdiff.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => t • V) V 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).smul_const V
  have hambient' :
      HasFDerivAt (cmp102AmbientNonlinearBlock U b)
        (fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0)
        ((0 : ℝ) • V) := by
    have hz : (0 : ℝ) • V = 0 := zero_smul ℝ V
    rw [hz]
    exact hambient
  have hcomp :
      HasDerivAt
        (fun t : ℝ => cmp102AmbientNonlinearBlock U b (t • V))
        (fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0 V) 0 := by
    simpa [Function.comp_def] using
      hambient'.comp_hasDerivAt 0 hline
  have hphysical :
      HasDerivAt
        (fun t : ℝ => cmp102AmbientNonlinearBlock U b (t • V))
        (deriv (cmp98Eq119NonlinearBlockCurve U A b) 0) 0 := by
    have hblock := hasDerivAt_cmp98Eq119NonlinearBlockCurve U A b hsmall
    have heq :
        (fun t : ℝ => cmp102AmbientNonlinearBlock U b (t • V)) =
          cmp98Eq119NonlinearBlockCurve U A b := by
      funext t
      exact cmp102AmbientNonlinearBlock_physicalLine_eq U A b t
    rw [heq]
    simpa only [hblock.deriv] using hblock
  exact hcomp.unique hphysical

/-- The physical right variation is a fixed ambient Fréchet derivative
followed by the common right-normalizing inverse. -/
theorem cmp98Eq119NonlinearRightVariation_eq_ambientFDeriv
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp98Eq119NonlinearRightVariation U A b =
      fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
          (physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) *
        cmp98Eq119NonlinearBlockInverseAtZero U A b := by
  unfold cmp98Eq119NonlinearRightVariation
  rw [fderiv_cmp102AmbientNonlinearBlock_zero_apply_physical
    U A b hsmall]

/-- Exact subtraction-linearity of the physical CMP98 right variation. -/
theorem cmp98Eq119NonlinearRightVariation_sub
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A B : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hsmall : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ < 1) :
    cmp98Eq119NonlinearRightVariation U (A - B) b =
      cmp98Eq119NonlinearRightVariation U A b -
        cmp98Eq119NonlinearRightVariation U B b := by
  rw [cmp98Eq119NonlinearRightVariation_eq_ambientFDeriv
      U (A - B) b hsmall,
    cmp98Eq119NonlinearRightVariation_eq_ambientFDeriv U A b hsmall,
    cmp98Eq119NonlinearRightVariation_eq_ambientFDeriv U B b hsmall]
  rw [cmp98Eq119NonlinearBlockInverseAtZero_twoField_eq U (A - B) A b,
    cmp98Eq119NonlinearBlockInverseAtZero_twoField_eq U A B b]
  let L := fderiv ℝ (cmp102AmbientNonlinearBlock U b) 0
  have hV :
      physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent (A - B)) =
        physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A) -
          physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent B) := by
    funext e i j
    simp [physicalSuTangentToAmbient,
      physicalCochainToSuMatrixTangent, PiLp.sub_apply, map_sub]
    change (_ - _ : Matrix (Fin Nc) (Fin Nc) ℂ) i j = _
    rfl
  change L
      (physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent (A - B))) * _ =
    L (physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A)) * _ -
      L (physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent B)) * _
  rw [hV, L.map_sub]
  noncomm_ring

end

end YangMills.RG
