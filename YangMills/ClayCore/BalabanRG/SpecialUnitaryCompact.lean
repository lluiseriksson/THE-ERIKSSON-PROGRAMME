import Mathlib
import YangMills.ClayCore.BalabanRG.SpecialUnitaryCompactUnconditional

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open Matrix

noncomputable section

/-- Public final compactness theorem for the local ambient `SU(m)` range. -/
theorem specialUnitary_compact_range_target
    (m : ℕ) :
    SpecialUnitaryCompactRangeTarget m := by
  exact specialUnitary_compact_unconditional m

/-- Public final topology package for the local ambient `SU(m)` range. -/
theorem specialUnitary_topology_gap_closed
    (m : ℕ) :
    SpecialUnitaryClosedTarget m ∧
      SpecialUnitaryEntrywiseBoundedTarget m ∧
      SpecialUnitaryCompactRangeTarget m := by
  exact specialUnitary_topology_package_unconditional m

end

end YangMills.ClayCore
