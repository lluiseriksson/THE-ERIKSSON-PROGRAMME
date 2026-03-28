/-!
# Haar-LSI Transfer — Explicit Witness

This file provides explicit witnesses for the two Haar-LSI transfer
propositions in the BalabanRG lane, and assembles the full
`HaarLSIFrontierPackage` closure.

## Key Observation

`HaarLSITarget n` (the *legacy weak* target) is defined as:

  `def HaarLSITarget (_n : ℕ) : Prop := ∃ α : ℝ, 0 < α`

This is a placeholder existence statement with no binding between α and
the actual LSI constant. Consequently `HaarLSIFromUniformLSITransfer n`
(the function type `SpecialUnitaryUniformLSIPackageTarget n → HaarLSITarget n`)
is trivially provable: extract `c > 0` from the hypothesis and use it as α.

## What This Closes

Together with `BalabanRGPackageWitness`, the full frontier package closes:

  `HaarLSIFrontierPackage d N_c`
  = `SpecialUnitaryScaleLSITarget d N_c ∧ HaarLSITarget N_c`

## Relation to the Analytic Target

The *mathematically substantive* Haar-LSI statement is
`HaarLSIAnalyticTarget N_c`, which carries the actual
`LogSobolevInequality (sunHaarProb N_c) (sunDirichletForm N_c) α_haar`
for a positive constant `α_haar`. That target is addressed in
`BalabanToLSI.lean` via axioms `bakry_emery_lsi` and `sun_bakry_emery_cd`.

The closure here only discharges the *weak placeholder* target.
-/

import YangMills.ClayCore.BalabanRG.HaarLSIBridge
import YangMills.ClayCore.BalabanRG.HaarLSIFrontier
import YangMills.ClayCore.BalabanRG.HaarLSIAnalyticTarget
import YangMills.ClayCore.BalabanRG.BalabanRGPackageWitness

namespace YangMills.ClayCore

/-!
## Section 1: Trivial Witness for HaarLSIFromUniformLSITransfer
-/

/-- **`HaarLSIFromUniformLSITransfer` is trivially provable.**

    `HaarLSITarget n = ∃ α : ℝ, 0 < α`, so we just extract `c > 0`
    from `SpecialUnitaryUniformLSIPackageTarget n = ∃ d c, 0 < c ∧ ...`
    and return it as the witness. -/
theorem haarLSIFromUniformLSITransfer_witness (n : ℕ) [NeZero n] :
    HaarLSIFromUniformLSITransfer n := by
  intro ⟨_d, c, hc, _⟩
  exact ⟨c, hc⟩

/-- **`HaarLSIFromUniformLSIAnalyticTransfer` for `N_c ≥ 2`.**

    P8 (`BalabanToLSI.lean`) already proves `HaarLSIAnalyticTarget N_c`
    unconditionally for `N_c ≥ 2` via axioms `bakry_emery_lsi` and
    `sun_bakry_emery_cd`. We can therefore ignore the uniform-LSI
    hypothesis entirely and use the P8 result directly. -/
theorem haarLSIFromUniformLSIAnalyticTransfer_witness (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    HaarLSIFromUniformLSIAnalyticTransfer n := by
  intro _
  exact analytic_haar_lsi_target_from_p8 n hn

/-!
## Section 2: Full Frontier Package Closure
-/

/-- **`HaarLSIFrontierPackage d N_c` is unconditionally closed**
    (for all `d N_c : ℕ` with `[NeZero N_c]`).

    Uses the minimal `BalabanRGPackage` witness from `BalabanRGPackageWitness.lean`
    and the trivial `HaarLSIFromUniformLSITransfer` witness above. -/
theorem haarLSIFrontierPackage_closed (d N_c : ℕ) [NeZero N_c] :
    HaarLSIFrontierPackage d N_c :=
  haar_lsi_frontier_package_of_pkg d N_c
    haarLSIFromUniformLSITransfer_witness
    (balabanRGPackage_minimalWitness d N_c)

/-- Bare `HaarLSITarget` is closed as a direct corollary. -/
theorem haarLSITarget_closed (N_c : ℕ) [NeZero N_c] : HaarLSITarget N_c :=
  (haarLSIFrontierPackage_closed 0 N_c).2

end YangMills.ClayCore
