import Mathlib.Analysis.Fourier.AddCircleMulti

namespace Step8b23AEFourierPhaseSumRepro

noncomputable section

def negativeTwoPiMomentum
    {d : ℕ} (t : Fin d → ℝ) : Fin d → ℂ :=
  fun mu ↦ -((2 * Real.pi : ℝ) : ℂ) * (t mu : ℂ)

theorem mFourier_neg_eq_exp_physicalPhase
    {d : ℕ} (n : Fin d → ℤ) (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (-n)
        (fun mu ↦ ((t mu : ℝ) : UnitAddCircle)) =
      Complex.exp (Complex.I *
        (∑ mu, negativeTwoPiMomentum t mu * (n mu : ℂ))) := by
  rw [UnitAddTorus.mFourier]
  simp only [ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_coe_apply, div_one]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  unfold negativeTwoPiMomentum
  push_cast
  ring

end

end Step8b23AEFourierPhaseSumRepro
