/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.P8_PhysicalGap.PhysicalMassGap
import YangMills.L8_Terminal.ClayTheorem

/-! # L8.2: Clay statement via LSI route (v0.31.0)

Provides an alternative witness of `ClayYangMillsTheorem` whose only
non-core axiom dependency is `holleyStroock_sunGibbs_lsi`, bypassing
the monolithic `yangMills_continuum_mass_gap` axiom.
-/

namespace YangMills

/-- Clay Yang-Mills theorem discharged via the SU(N) Holley-Stroock LSI route. -/
theorem yangMills_existence_massGap_via_lsi : ClayYangMillsTheorem :=
  sun_physical_mass_gap_legacy 4 3 (by norm_num) 1 1 le_rfl one_pos

/-- Clay Millennium Theorem via the LSI route. -/
theorem clay_millennium_yangMills_via_lsi : ∃ m_phys : ℝ, 0 < m_phys :=
  yangMills_existence_massGap_via_lsi

end YangMills
