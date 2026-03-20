import Mathlib

open scoped BigOperators
open Classical

/-!
Recon local para descubrir los nombres reales disponibles en esta snapshot
de Mathlib antes de cerrar la prueba de compacidad de SU(N).
-/

#check Matrix
#check Matrix.SpecialLinearGroup
#check Matrix.GeneralLinearGroup
#check unitary
#check IsCompact
#check Bornology.IsBounded
#check Finite
#check Fintype
#check Matrix.det
#check Continuous
#check ContinuousOn
#check IsClosed
#check Metric.isCompact_iff_isClosed_bounded

-- candidatos habituales; algunos fallarán y eso está bien, queremos el nombre exacto:
#check Matrix.unitaryGroup
#check Matrix.UnitaryGroup
#check unitaryGroup
#check UnitaryGroup
#check specialUnitaryGroup
#check SpecialUnitaryGroup

namespace YangMills.ClayCore

-- placeholder para forzar import/build dentro del proyecto
theorem mathlib_topology_recon_placeholder : True := by
  trivial

end YangMills.ClayCore
