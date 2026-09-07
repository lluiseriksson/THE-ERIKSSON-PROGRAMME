import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! PRE-VALIDATION: exact generic rewrite repro before the physical retry. -/
open MeasureTheory
namespace YangMills.RG
noncomputable section

def neumannReproNormalizedIntegral (mu : Measure (Fin 4 → ℝ)) (k : ℂ)
    (f : (Fin 4 → ℝ) → ℂ) : ℂ := k * ∫ x, f x ∂mu

theorem neumannReproNormalizedIntegral_mul (mu : Measure (Fin 4 → ℝ))
    (k c : ℂ) (f : (Fin 4 → ℝ) → ℂ) :
    neumannReproNormalizedIntegral mu k (fun x => f x * c) =
      neumannReproNormalizedIntegral mu k f * c := by
  unfold neumannReproNormalizedIntegral
  dsimp only
  rw [MeasureTheory.integral_mul_const (μ := mu) c f, mul_assoc]

theorem neumannReproDependentZeroIf (u v : Fin 4 → ℤ) (c : ℂ)
    (h : u = 0 ↔ v = 0) :
    (if v = 0 then (1 : ℂ) else 0) * c = if u = 0 then c else 0 := by
  classical
  by_cases hv0 : v = 0
  · have hu0 := h.mpr hv0
    simp [hv0, hu0]
  · have hu0 : u ≠ 0 := fun hu => hv0 (h.mp hu)
    simp [hv0, hu0]

theorem neumannReproZeroCast (N : ℕ) :
    (fun i : Fin 4 => ((0 : Fin 4 → ℤ) i : ZMod N)) = 0 := by
  funext i
  simp

end
end YangMills.RG

#print axioms YangMills.RG.neumannReproNormalizedIntegral_mul
#print axioms YangMills.RG.neumannReproDependentZeroIf
#print axioms YangMills.RG.neumannReproZeroCast
