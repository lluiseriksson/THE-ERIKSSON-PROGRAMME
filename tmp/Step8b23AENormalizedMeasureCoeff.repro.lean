import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open scoped ENNReal

example (I : ℂ) :
    (ENNReal.ofReal (Real.pi⁻¹ * (2 : ℝ)⁻¹)).toReal ^ 4 • I =
      (((2 : ℂ) * Real.pi) ^ 4)⁻¹ * I := by
  have hc : 0 ≤ Real.pi⁻¹ * (2 : ℝ)⁻¹ := by positivity
  have hcoeff :
      (Real.pi⁻¹ * (2 : ℝ)⁻¹) ^ 4 = ((2 * Real.pi) ^ 4)⁻¹ := by
    field_simp [Real.pi_ne_zero]
  rw [ENNReal.toReal_ofReal hc, hcoeff, Complex.real_smul]
  norm_cast
