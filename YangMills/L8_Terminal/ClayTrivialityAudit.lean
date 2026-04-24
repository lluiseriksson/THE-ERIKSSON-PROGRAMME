/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L8_Terminal.ClayTheorem

/-!
# L8: Clay-endpoint triviality audit canary (v0.47.0)

Records, as a first-class Lean theorem, the observation already
documented in `TestC72Proto.lean:31-32` (comment) and
`L8_Terminal/ClayPhysical.lean:206-210` (hierarchy):

    `ClayYangMillsTheorem := ∃ m_phys : ℝ, 0 < m_phys`

is trivially inhabited.

Equivalently, it is logically equivalent to `True`.

Any theorem whose conclusion is `ClayYangMillsTheorem` therefore
discharges only this weak existential, not Clay-grade Yang-Mills
content. The authentic target hierarchy is

    `ClayYangMillsPhysicalStrong → ClayYangMillsStrong → ClayYangMillsTheorem`

with `ClayYangMillsPhysicalStrong` the first non-vacuous level
(see `L8_Terminal/ClayPhysical.lean:89-91`).

Purpose: forward tripwire. `#print axioms` on the canary is
expected to be empty `[]` or a subset of the canonical project
oracle `[propext, Classical.choice, Quot.sound]`; the exact trace
is pinned in AXIOM_FRONTIER.md v0.47.0 after first successful
build. Any future refactor that accidentally narrows a Clay
endpoint to `ClayYangMillsTheorem` will be visible at audit time
because this canary discharges it with zero hypotheses.

See `AXIOM_FRONTIER.md` v0.47.0 for the full recording.

No sorry. No new axioms.
-/

namespace YangMills

/-- **Audit canary.** `ClayYangMillsTheorem` is trivially inhabited
    by `⟨1, one_pos⟩`. Any theorem whose conclusion is
    `ClayYangMillsTheorem` discharges only this weak existential;
    real Clay content lives in `ClayYangMillsPhysicalStrong` and its
    gauge-content intermediate `ClayYangMillsMassGap N_c`.

    This exists to make weak endpoints visible at audit time. -/
theorem clayYangMillsTheorem_trivial : ClayYangMillsTheorem :=
  ⟨1, one_pos⟩

/-- **Audit canary, strengthened.** The weak endpoint
    `ClayYangMillsTheorem` is logically equivalent to `True`.

    This makes the audit invariant explicit: landing a theorem whose
    terminal conclusion is only `ClayYangMillsTheorem` cannot, by itself,
    be counted as a non-vacuous Clay-grade closure. -/
theorem clayYangMillsTheorem_iff_true : ClayYangMillsTheorem ↔ True :=
  ⟨fun _ => trivial, fun _ => clayYangMillsTheorem_trivial⟩

#print axioms clayYangMillsTheorem_trivial
#print axioms clayYangMillsTheorem_iff_true

end YangMills
