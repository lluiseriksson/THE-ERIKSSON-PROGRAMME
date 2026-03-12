import Mathlib

#check @instTopologicalGroupSubtypeMemSubmonoid
example : ∃ _ : TopologicalSpace (Matrix.unitaryGroup (Fin 2) ℂ), True := ⟨inferInstance, trivial⟩

-- Search for TopologicalGroup
#check (inferInstance : TopologicalSpace (Matrix.unitaryGroup (Fin 2) ℂ))
open scoped Topology in
#check (Matrix.unitaryGroup (Fin 2) ℂ)
