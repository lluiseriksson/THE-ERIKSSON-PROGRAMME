import Mathlib
import YangMills.ClayCore.BalabanRG.SpecialUnitaryClosedEntrywiseBoundedToCompact

namespace YangMills.ClayCore

open scoped BigOperators
open Classical
open Matrix

noncomputable section

/-!
# SpecialUnitaryCompactUnconditional — final unconditional façade

This file exposes the final unconditional topological package for the local
`SU(m)` range, now that the closedness proof, the entrywise bounded proof, and
the honest transfer to compactness all live inside the repo.
-/

/-- Final unconditional compactness theorem for the local `SU(m)` range. -/
theorem specialUnitary_compact_unconditional
    (m : ℕ) :
    SpecialUnitaryCompactRangeTarget m := by
  exact specialUnitary_compact_range_target_unconditional m

/-- Final unconditional topology package for the local `SU(m)` range. -/
theorem specialUnitary_topology_package_unconditional
    (m : ℕ) :
    SpecialUnitaryClosedTarget m ∧
      SpecialUnitaryEntrywiseBoundedTarget m ∧
      SpecialUnitaryCompactRangeTarget m := by
  exact specialUnitary_topology_gap_closed_unconditional m

end

end YangMills.ClayCore
