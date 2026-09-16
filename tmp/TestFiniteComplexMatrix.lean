import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import YangMills.RG.BalabanCMP116PhysicalEndomorphismMatrix

#synth FiniteDimensional ℝ ℂ
#synth FiniteDimensional ℝ (Fin 2 → ℂ)
#synth FiniteDimensional ℝ (Matrix (Fin 2) (Fin 2) ℂ)
#check @LinearMap.continuous_of_finiteDimensional
#check Module.Finite.matrix

open YangMills.RG

example {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] :
    Fintype (CMP116PhysicalWalkCoordinate d N Nc) := by infer_instance

example {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)] :
    FiniteDimensional ℝ
      (Matrix (CMP116PhysicalWalkCoordinate d N Nc)
        (CMP116PhysicalWalkCoordinate d N Nc) ℂ) := by
  exact Module.Finite.matrix
