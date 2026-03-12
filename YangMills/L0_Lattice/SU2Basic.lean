import Mathlib

noncomputable section

namespace YangMills

/-- SU(2) as the special unitary group. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

instance : Group SU2 := inferInstance
instance : TopologicalSpace SU2 := inferInstance
instance : ContinuousMul SU2 := inferInstance

end YangMills

end
