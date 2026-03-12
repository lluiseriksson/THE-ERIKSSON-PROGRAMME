import Mathlib

-- What instances does unitaryGroup have?
#synth TopologicalSpace (Matrix.unitaryGroup (Fin 2) ℂ)
#synth Group (Matrix.unitaryGroup (Fin 2) ℂ)
#synth ContinuousMul (Matrix.unitaryGroup (Fin 2) ℂ)
#synth ContinuousInv (Matrix.unitaryGroup (Fin 2) ℂ)
