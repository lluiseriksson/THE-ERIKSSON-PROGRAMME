import Mathlib.LinearAlgebra.Complex.FiniteDimensional

local instance : ContinuousSMul ℝ ℂ := {
  continuous_smul := by
    simpa [Complex.real_smul] using
      (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
}

#synth Module ℝ (Matrix (Fin 2) (Fin 3) ℂ)
#synth FiniteDimensional ℝ (Matrix (Fin 2) (Fin 3) ℂ)

example (r : ℝ) (A : Matrix (Fin 2) (Fin 3) ℂ) (i j) :
    ((r • A) i j).re = r * (A i j).re := by
  change (r • A i j).re = _
  rw [Complex.real_smul]
  simp
