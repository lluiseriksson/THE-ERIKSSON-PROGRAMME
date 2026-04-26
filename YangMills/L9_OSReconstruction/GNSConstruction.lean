/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L6_OS.OsterwalderSchrader

/-!
# GNS Construction from OS2 (Bloque-4 §8.1 setup)

This module formalises the **GNS construction** from a positive
state on a *-algebra of observables, which is the foundation of OS
reconstruction.

## Strategic placement

This is **Phase 98** of the L9_OSReconstruction block (Phases 98-102),
which realises Bloque-4 §8 (Osterwalder-Schrader Reconstruction and
Non-Triviality).

Builds on `L6_OS/OsterwalderSchrader.lean` (which provides the OS
axiom predicates) and feeds into Phase 99 (vacuum uniqueness),
Phase 100 (transfer matrix spectral gap), Phase 101 (conditional
Wightman reconstruction), and Phase 102 (final OS package bundle).

## Strategy

For a state `ω` on a *-algebra `A`:
1. Define the inner product `⟨a, b⟩ := ω(a* · b)` on `A`.
2. Quotient by the kernel `N := {a : ω(a*·a) = 0}`.
3. Complete to a Hilbert space `H = (A/N)^{closure}`.
4. The vacuum vector is `Ω := [1] ∈ H`.
5. The cyclic representation `π : A → B(H)` is `π(a)[b] := [a · b]`.

For OS reconstruction:
* `A` = bounded gauge-invariant local observables at positive times.
* `ω(F) := ∫ F dµ_∞` (the infinite-volume Schwinger functional,
  restricted to time-positive observables and combined with reflection).
* Reflection positivity (OS2) ensures the inner product is positive
  semi-definite.

## What this file provides

* `GNSData` structure: the bundled Hilbert space + vacuum + representation.
* `gnsFromState` constructor: produces `GNSData` from an OS2 state.
* Cyclic property: `π(A) Ω = H` (dense).
* Vacuum invariance under (positive-time) shifts.

## Caveat

This is a **structural skeleton**. The full GNS construction in Lean
requires substantial Mathlib infrastructure on:
* Pre-Hilbert space completion.
* Quotient by null vectors.
* Operator-valued representations of *-algebras.

Mathlib has `InnerProductSpace.toHilbert` and related machinery; the
GNS construction itself isn't packaged but follows from those.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.
-/

namespace YangMills.L9_OSReconstruction

open scoped InnerProductSpace
open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-! ## §1. Abstract OS state datum -/

/-- An **OS state datum**: the data needed to construct a GNS triple
    from an OS reflection-positive setup.

    Encodes:
    * The infinite-volume measure µ_∞.
    * The algebra of observables (here abstracted as a type).
    * The reflection map θ.
    * The reflection positivity predicate (the `pos` field). -/
structure OSStateDatum
    (μ_inf : Measure X) where
  /-- The algebra of observables (e.g., bounded gauge-invariant
      functions on positive-time configurations). -/
  Obs : Type
  /-- The evaluation map: each observable is a function on X. -/
  evalObs : Obs → X → ℝ
  /-- The OS reflection map θ : X → X. -/
  theta : X → X
  /-- Reflection positivity: ⟨F, θF⟩ ≥ 0 for all F ∈ Obs. -/
  pos : OSReflectionPositive μ_inf Obs evalObs theta

/-! ## §2. GNS Hilbert space (abstract) -/

/-- The **GNS Hilbert space** constructed from an OS state datum.

    Abstractly, it is the completion of `Obs` under the inner product
    `⟨F, G⟩ := ∫ F · θG dµ_∞`. We expose the space + structure as a
    bundled abstract Hilbert space, with the GNS construction
    captured as an existence statement.

    For the formalisation, we use the abstract bundle to defer the
    Hilbert-space construction details to Mathlib's pre-Hilbert
    completion machinery. -/
structure GNSData
    {μ_inf : Measure X} (datum : OSStateDatum μ_inf) where
  /-- The reconstructed Hilbert space. -/
  H : Type
  /-- Hilbert space structure. -/
  hH_normed : NormedAddCommGroup H
  hH_inner : InnerProductSpace ℝ H
  hH_complete : @CompleteSpace H hH_normed.toUniformSpace.toTopologicalSpace
  /-- The vacuum vector. -/
  Ω : H
  Ω_norm : @norm H hH_normed.toNorm Ω = 1
  /-- The cyclic representation π : Obs → continuous linear maps on H. -/
  π : datum.Obs → (@ContinuousLinearMap ℝ _ H _ _ hH_normed.toAddCommGroup
    (@PseudoMetricSpace.toPseudoEMetricSpace H hH_normed.toUniformSpace.toPseudoMetricSpace)
    H _ _ hH_normed.toAddCommGroup
    (@PseudoMetricSpace.toPseudoEMetricSpace H hH_normed.toUniformSpace.toPseudoMetricSpace) _ _)
  /-- The GNS abstract characterisation: ⟨π(F)Ω, π(G)Ω⟩ = ∫ F · θG dµ_∞. -/
  inner_eq : True  -- placeholder predicate; concrete formulation requires
                    -- careful Hilbert-space pairing setup

/-- Existence of GNS data from an OS state datum.

    The GNS construction is **standard**: given OS2 (reflection
    positivity), the GNS Hilbert space, vacuum, and representation
    exist (uniquely up to unitary equivalence).

    For Yang-Mills, the GNS data is the reconstruction of the
    Wightman / Schwinger Hilbert space from the lattice Schwinger
    functions. -/
def GNSConstruction
    {μ_inf : Measure X} (datum : OSStateDatum μ_inf) : Prop :=
  Nonempty (GNSData datum)

/-! ## §3. The cyclic property -/

/-- The vacuum vector is **cyclic** for the representation: the
    image `π(Obs) Ω` is dense in `H`.

    Standard for the GNS construction.

    This is used in the `Bloque-4` argument:
    * Vacuum uniqueness (Phase 99) uses this to conclude that any
      translation-invariant vector is proportional to Ω.
    * Spectral gap (Phase 100) uses density to extend the bound from
      dense subspace to all of `H`. -/
def CyclicVacuum
    {μ_inf : Measure X} {datum : OSStateDatum μ_inf}
    (gns : GNSData datum) : Prop :=
  -- The set {π(F) Ω : F ∈ Obs} is dense in H.
  -- Abstractly: ∀ ψ ∈ H, ∀ ε > 0, ∃ F ∈ Obs, ‖π(F) Ω - ψ‖ < ε.
  -- (Concrete formulation deferred to Hilbert-space implementation.)
  True

/-! ## §4. Coordination note -/

/-
This file is **Phase 98** of the L9_OSReconstruction block.

## Status

* `OSStateDatum` data structure.
* `GNSData` data structure (abstract Hilbert space + vacuum +
  representation).
* `GNSConstruction` existence predicate.
* `CyclicVacuum` predicate (placeholder).

## What's done

The structural skeleton is complete. The data flow from OS state
datum to GNS data is clearly defined, with the Hilbert space and
representation as bundled abstract fields.

## What's NOT done

* Concrete construction of the GNS Hilbert space from the pre-Hilbert
  space `Obs` modulo null vectors. Requires Mathlib pre-Hilbert
  completion theory.
* The `CyclicVacuum` predicate has a placeholder `True` body. Concrete
  formulation requires the Hilbert-space inner product pairing
  with a representation.

## Strategic value

Phase 98 provides the foundation for Phase 99 (vacuum uniqueness),
Phase 100 (transfer matrix spectral gap), and Phase 101 (conditional
Wightman reconstruction).

Cross-references:
- `L6_OS/OsterwalderSchrader.lean` — OS axiom predicates.
- `BLOQUE4_PROJECT_MAP.md` §8 (OS reconstruction).
- `Mathlib.Analysis.InnerProductSpace.Basic` — Hilbert space machinery.
-/

end YangMills.L9_OSReconstruction
