/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.AbelianU1Unconditional
import YangMills.L6_OS.OsterwalderSchrader

/-!
# SU(1) discharge of `OSClusterProperty` (Branch I cluster terminus)

This module provides an **unconditional discharge** of the abstract
OS-cluster predicate `OSClusterProperty` (defined in
`L6_OS/OsterwalderSchrader.lean`) for the SU(1) Wilson Gibbs measure.

## Why it works for SU(1)

The OS cluster property states:
```
∃ C m, 0 ≤ C ∧ 0 < m ∧
  ∀ O1 O2, |⟨O1·O2⟩ - ⟨O1⟩·⟨O2⟩| ≤ C · exp(-m · dist O1 O2)
```

For SU(1):

1. `GaugeConfig d L SU(1)` is `Subsingleton` (every config is the
   trivial all-identity configuration).
2. So **every** real-valued function on `GaugeConfig d L SU(1)` is
   constant, including `fun U => evalObs O U`.
3. The Wilson Gibbs measure is a probability measure (instance
   `gibbs_su1_isProbability` from `AbelianU1Unconditional`).
4. Integrating a constant against a probability measure returns the
   constant.
5. So `⟨O1·O2⟩ = (evalObs O1 U₀) · (evalObs O2 U₀)` and
   `⟨O1⟩·⟨O2⟩ = (evalObs O1 U₀) · (evalObs O2 U₀)`.
   Their difference is `0`.
6. `|0| = 0 ≤ 0 · exp(...) = 0` is the trivial bound. Take `C := 0`,
   `m := 1`.

The proof uses NO measurability assumption on `evalObs`: integrals of
constants (after pointwise replacement on a Subsingleton) are evaluated
via `integral_const` and the probability normalisation `μ univ = 1`.

## Caveat

Per `COWORK_FINDINGS.md` Finding 003, SU(1) here is the **trivial**
group `{1}`, not abelian U(1) gauge theory. The cluster property
holds because the entire dynamics collapses to a point: this witness
is **structurally non-vacuous** at the predicate-type level (an
honest inhabitant of `OSClusterProperty`) but **physics-degenerate**
(no real Wilson dynamics exist).

For `N_c ≥ 2`, OS clustering becomes a substantive measure-theoretic
obligation, typically proved via the L4 large-field cluster expansion
or the Bałaban-Magnen-Rivasseau analytic ladder.

## Oracle target

`[propext, Classical.choice, Quot.sound]` per project discipline.

-/

namespace YangMills.L6_OS

open MeasureTheory

variable {d L : ℕ} [NeZero d] [NeZero L]

/-! ## §1. Subsingleton-integral helper for SU(1) -/

/-- Integral of any real-valued function on the SU(1) gauge-config space
    against any probability measure equals the function evaluated at the
    canonical (`default`) configuration.

    Proof: `GaugeConfig d L SU(1)` is `Subsingleton`, so the function
    equals the constant `fun _ => f default` pointwise. Then
    `integral_const` plus probability-measure normalisation closes. -/
private lemma integral_eq_default_su1
    {μ : Measure (GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ))}
    [IsProbabilityMeasure μ]
    (f : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ) :
    (∫ U, f U ∂μ) = f default := by
  have h :
      (fun U : GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) => f U) =
      (fun _ => f default) := by
    funext U
    rw [Subsingleton.elim U default]
  rw [h]
  simp

/-! ## §2. SU(1) OS cluster property — unconditional -/

/-- **`OSClusterProperty` discharged unconditionally for SU(1)**, with
    arbitrary observable type `Obs`, arbitrary evaluation
    `evalObs : Obs → X → ℝ`, and arbitrary `distObs`.

    Witness constants: `C := 0`, `m := 1`.

    The connected correlator `⟨O1·O2⟩ - ⟨O1⟩·⟨O2⟩` reduces to
    `(evalObs O1 default · evalObs O2 default) -
     (evalObs O1 default · evalObs O2 default) = 0` using
    `integral_eq_default_su1`. The bound becomes `|0| ≤ 0 · exp(...)`
    which is `0 ≤ 0`. -/
theorem osClusterProperty_su1
    (β : ℝ) (Obs : Type*)
    (evalObs : Obs → GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (distObs : Obs → Obs → ℝ) :
    OSClusterProperty
      (gibbsMeasure (d := d) (N := L)
        (sunHaarProb 1) (wilsonPlaquetteEnergy 1) β)
      Obs evalObs distObs := by
  refine ⟨0, 1, le_refl 0, one_pos, ?_⟩
  intro O1 O2
  rw [integral_eq_default_su1 (fun U => evalObs O1 U * evalObs O2 U),
      integral_eq_default_su1 (fun U => evalObs O1 U),
      integral_eq_default_su1 (fun U => evalObs O2 U)]
  simp

#print axioms osClusterProperty_su1

/-! ## §3. Mass-gap corollary via the OS terminal theorem -/

/-- **Existence of a positive mass via SU(1) OS clustering** —
    composes the unconditional `osClusterProperty_su1` witness with
    the project's terminal extraction `osCluster_implies_massGap`
    from `OsterwalderSchrader.lean`. Yields `∃ m, 0 < m`
    unconditionally.

    Note: as in the Branch III RP discharge (Phase 46), this is a
    structural (non-physical) inhabitant of the existential — the
    underlying mass is `1` by construction, set in `osClusterProperty_su1`. -/
theorem osMassGap_su1_unconditional
    (β : ℝ) (Obs : Type*)
    (evalObs : Obs → GaugeConfig d L ↥(Matrix.specialUnitaryGroup (Fin 1) ℂ) → ℝ)
    (distObs : Obs → Obs → ℝ) :
    ∃ m : ℝ, 0 < m :=
  YangMills.osCluster_implies_massGap _ _ _ _
    (osClusterProperty_su1 (d := d) (L := L) β Obs evalObs distObs)

#print axioms osMassGap_su1_unconditional

/-! ## §4. Coordination note -/

/-
This file extends the SU(1) unconditional witness chain into the
**OS-cluster** terminus on Branch I:

```
SU(1) unconditional ladder (cumulative):
  ClayYangMillsTheorem                         — derivable
  ClayYangMillsMassGap 1                       — Phase 7.2 (2026-04-23)
  ClayYangMillsPhysicalStrong (1, β, F, …)     — Phase 43 (2026-04-25)
  ClayYangMillsPhysicalStrong_Genuine (1, …)   — Phase 45 (2026-04-25) ⭐
  wilsonGibbs_reflectionPositive (Branch III)  — Phase 46 (2026-04-25)
  OSReflectionPositive (Branch III, OS-form)   — Phase 47 (2026-04-25)
  OSClusterProperty (Branch I, OS-form)        — Phase 49 (2026-04-25) — THIS FILE
```

Together with the Branch III RP discharge (`AbelianU1Reflection.lean`),
this file demonstrates that **both** OS axioms relevant to mass-gap
extraction (RP and clustering) admit unconditional SU(1) inhabitants.
The trivial-group physics-degeneracy caveat applies (Finding 003).

For `N_c ≥ 2`, OS clustering and OS-RP both become substantive
measure-theoretic obligations:
* RP: handled by the Osterwalder-Seiler 1978 / Glimm-Jaffe construction.
* Clustering: handled by the L4 cluster expansion (small β) and the
  Branch III TM spectral-gap pipeline (all β, conditioned on
  semigroup-generator theory).

Cross-references:
- `OsterwalderSchrader.lean` — `OSClusterProperty` definition and
  `osCluster_implies_massGap` extraction.
- `AbelianU1Unconditional.lean` — SU(1) Subsingleton instances and
  `gibbs_su1_isProbability`.
- `AbelianU1Reflection.lean` — Phase 46 RP companion file.
- `COWORK_FINDINGS.md` Finding 003 — SU(1) physics-degeneracy caveat.
-/

end YangMills.L6_OS
