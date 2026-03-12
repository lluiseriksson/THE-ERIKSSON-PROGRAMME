import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Matrix

namespace YangMills

/-- SU(2) structured as the special unitary group. -/
abbrev SU2 := Matrix.SpecialUnitaryGroup (Fin 2) ℂ

instance : Group SU2 := inferInstance

instance : TopologicalSpace SU2 := inferInstance

instance : TopologicalGroup SU2 := inferInstance

instance : CompactSpace SU2 := inferInstance

end YangMills
