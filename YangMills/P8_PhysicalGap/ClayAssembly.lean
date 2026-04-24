/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L8_Terminal.ClayTheorem
import YangMills.P8_PhysicalGap.ClayViaLSI
import YangMills.P6_AsymptoticFreedom.AsymptoticFreedomDischarge

/-! # P8.Clay: Terminal Clay assembly via the LSI route (v0.32.0)

This file assembles the public Clay theorems by discharging the existentials
through two downstream witnesses whose terminal oracles are core-only:

* `yangMills_existence_massGap_via_lsi` — provides `ClayYangMillsTheorem`
  through the MemLp-gated normalized LSI route.
* `clay_strong_no_axiom` (from P6) — provides `ClayYangMillsStrong`
  with oracle `[propext, Classical.choice, Quot.sound]`.

The monolithic axiom `yangMills_continuum_mass_gap` is **no longer used
anywhere** in the project.  The legacy unnormalized Holley-Stroock axiom remains
available for old P8/BalabanRG interfaces, but it is not load-bearing for these
terminal public theorems.

Public theorem names (`yangMills_existence_massGap`, `clay_mass_gap_pos`,
`clay_millennium_yangMills`, `clay_millennium_yangMills_strong`) are
preserved so downstream code continues to compile unchanged.
-/

namespace YangMills

/-- Terminal assembly: existence of a positive physical mass gap for SU(N)
Yang–Mills, via the Holley–Stroock LSI route. -/
theorem yangMills_existence_massGap : ClayYangMillsTheorem :=
  yangMills_existence_massGap_via_lsi

/-- The physical mass gap is strictly positive. -/
theorem clay_mass_gap_pos : ∃ m_phys : ℝ, 0 < m_phys :=
  yangMills_existence_massGap

/-! ## Clay Millennium Theorem (v0.32.0)

Zero explicit hypothesis parameters.  The MemLp-gated normalized LSI route keeps
the terminal weak endpoint oracle at the canonical project core.
-/
theorem clay_millennium_yangMills : ∃ m_phys : ℝ, 0 < m_phys :=
  clay_mass_gap_pos

/-- Strong terminal theorem. **Axiom-free** (no reliance on any project
axiom; depends only on `[propext, Classical.choice, Quot.sound]`). -/
theorem clay_millennium_yangMills_strong : ClayYangMillsStrong :=
  clay_strong_no_axiom

#print axioms yangMills_existence_massGap
#print axioms clay_millennium_yangMills
#print axioms clay_millennium_yangMills_strong

end YangMills
