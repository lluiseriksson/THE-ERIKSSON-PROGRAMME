import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! PRE-VALIDATION: inspect the exact integral types; no physical claim. -/
open MeasureTheory
namespace YangMills.RG
noncomputable section

set_option pp.all true in
theorem neumannIntegralTypeProbe (mu : Measure (Fin 4 → ℝ))
    (c : ℂ) (f : (Fin 4 → ℝ) → ℂ) :
    (∫ x, f x * c ∂mu) = (∫ x, f x ∂mu) * c := by
  exact MeasureTheory.integral_mul_const (μ := mu) c f

end
end YangMills.RG

#print axioms YangMills.RG.neumannIntegralTypeProbe
