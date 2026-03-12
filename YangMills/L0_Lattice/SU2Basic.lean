import Mathlib

namespace YangMills

/-- SU(2) as the special unitary group. -/
noncomputable abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

noncomputable instance : Group SU2 := inferInstance
instance : TopologicalSpace SU2 := inferInstance
instance : TopologicalGroup SU2 := inferInstance
instance : CompactSpace SU2 := by
  have : CompactSpace (Matrix.unitaryGroup (Fin 2) ℂ) := inferInstance
  exact inferInstance

end YangMills
