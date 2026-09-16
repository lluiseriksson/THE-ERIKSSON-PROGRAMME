import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! PRE-VALIDATION: uncompiled Mathlib-only repro for the literal physical
endpoint scale algebra. No physical theorem or production output claimed. -/

namespace YangMills.RG
noncomputable section

theorem neumannPhysicalEndpointPhase_repro
    (N : ℕ) (z : Fin 4 → ℂ) (m target source : Fin 4 → ℤ) :
    Complex.I *
      ((∑ i, (z i + ((2 * Real.pi * (m i : ℝ) : ℝ) : ℂ)) *
        (((((N : ℝ)⁻¹) * (target i : ℝ)) : ℝ) : ℂ)) -
       (∑ i, (z i + ((2 * Real.pi * (m i : ℝ) : ℝ) : ℂ)) *
        (((((N : ℝ)⁻¹) * (source i : ℝ)) : ℝ) : ℂ))) =
      ∑ i, Complex.I * (z i + 2 * Real.pi * (m i : ℂ)) *
        ((target - source) i : ℂ) / (N : ℂ) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  push_cast
  ring

end
end YangMills.RG

#print axioms YangMills.RG.neumannPhysicalEndpointPhase_repro
