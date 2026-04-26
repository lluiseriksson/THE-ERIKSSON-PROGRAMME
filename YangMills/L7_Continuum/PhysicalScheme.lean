/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.L7_Continuum.ContinuumLimit

/-!
# Physical lattice-spacing scheme — Cowork Branch VII (continuum limit)

This module implements the **honest** continuum-limit framework
for SU(N_c) Yang-Mills, addressing `COWORK_FINDINGS.md` Finding 004.

The existing `HasContinuumMassGap m_lat` in
`YangMills/L7_Continuum/ContinuumLimit.lean` is satisfied by the
coordinated-scaling artifact `latticeSpacing N = 1/(N+1)` paired
with `constantMassProfile m N = m/(N+1)`. This is structurally
honest at the Lean level but does not encode genuine continuum
analysis.

This module introduces:

* `PhysicalLatticeScheme N_c` — a structure encoding the
  asymptotic-freedom lattice-spacing scheme for SU(N_c).
* `HasContinuumMassGap_Genuine` — the genuine continuum-mass-gap
  predicate using a `PhysicalLatticeScheme`.
* `ClayYangMillsPhysicalStrong_Genuine` — the genuine Clay-grade
  predicate.

These are intentionally **stronger** than the existing predicates.
The existing ones are NOT implied by the genuine ones (different
parametrisation), but the genuine ones strictly imply the existing
ones (by taking a suitable spacing function).

## Status

This file is a **scaffold**: predicate definitions + key
non-implication observations + sorry-ed witness obligations.
The substantive Lean proofs require composition with the F3
chain (Codex's Branch I) plus the asymptotic-freedom framework
in `YangMills/P6_AsymptoticFreedom/`.

See `BLUEPRINT_ContinuumLimit.md` for the full strategic plan.

## Oracle target

Per project discipline (`CODEX_CONSTRAINT_CONTRACT.md` HR5),
every theorem in this file should print
`[propext, Classical.choice, Quot.sound]`. Sorries are explicit
where the witness work has not been done.

-/

namespace YangMills.Continuum

open Real Filter Topology

/-! ### One-loop β-function coefficient -/

/-- One-loop β-function coefficient for SU(N_c) Yang-Mills.

`b₀(N_c) = 11 N_c / (48 π²)`

This is the asymptotic-freedom coefficient: positive for all
`N_c ≥ 1`, governing the leading running of the gauge coupling.

Reference: Politzer 1973 / Gross-Wilczek 1973, original
asymptotic-freedom papers. The lattice version appears in
Bałaban CMP 122 (1989). -/
noncomputable def b0 (N_c : ℕ) : ℝ :=
  (11 : ℝ) * N_c / (48 * Real.pi ^ 2)

/-- `b₀` is strictly positive for `N_c ≥ 1`. -/
theorem b0_pos (N_c : ℕ) (h : 1 ≤ N_c) : 0 < b0 N_c := by
  unfold b0
  have h1 : (0 : ℝ) < 11 * N_c := by
    have : (1 : ℝ) ≤ N_c := by exact_mod_cast h
    linarith
  have h2 : (0 : ℝ) < 48 * Real.pi ^ 2 := by
    have : 0 < Real.pi := Real.pi_pos
    positivity
  exact div_pos h1 h2

/-! ### Physical lattice-spacing scheme -/

/-- A **physical** lattice-spacing scheme for SU(N_c) Yang-Mills.

This is NOT just any positive function `N → ℝ` (as
`HasContinuumMassGap` allows). Instead, it carries:

- A lattice spacing `a : ℕ → ℝ` tending to 0 (the continuum
  limit).
- A lattice coupling `g : ℕ → ℝ` tending to 0 (asymptotic
  freedom).
- The asymptotic-freedom RG relation between `a` and `g`:
  `a(N) ~ (1/Λ) · exp(-1 / (2 b₀ g(N)²))` as `N → ∞`,
  for some QCD scale `Λ > 0`.

The relation is asymptotic (held in the limit) rather than exact,
to allow for higher-loop corrections. -/
structure PhysicalLatticeScheme (N_c : ℕ) [NeZero N_c] where
  /-- Lattice spacing as a function of resolution `N`. -/
  a : ℕ → ℝ
  /-- Strict positivity. -/
  ha_pos : ∀ N, 0 < a N
  /-- Continuum limit: `a(N) → 0` as `N → ∞`. -/
  ha_tends_zero : Tendsto a atTop (𝓝 0)
  /-- The lattice coupling at each resolution. -/
  g : ℕ → ℝ
  /-- Coupling positivity. -/
  hg_pos : ∀ N, 0 < g N
  /-- Asymptotic freedom: `g(N) → 0` as `N → ∞`. -/
  hg_asymp_free : Tendsto g atTop (𝓝 0)
  /-- The asymptotic RG relation between `a` and `g`:
      `a(N) · exp(1/(2 b₀ g(N)²)) → 1/Λ`. -/
  ha_g_relation :
    ∃ Λ : ℝ, 0 < Λ ∧
    Tendsto (fun N => a N * Real.exp (1 / (2 * b0 N_c * (g N)^2)))
      atTop (𝓝 (1 / Λ))

namespace PhysicalLatticeScheme

variable {N_c : ℕ} [NeZero N_c]

/-- A `PhysicalLatticeScheme` produces a `LatticeMassProfile`-style
    spacing function (the underlying `a`). -/
noncomputable def toSpacingFunction (scheme : PhysicalLatticeScheme N_c) :
    ℕ → ℝ :=
  scheme.a

theorem toSpacingFunction_pos (scheme : PhysicalLatticeScheme N_c) (N : ℕ) :
    0 < scheme.toSpacingFunction N :=
  scheme.ha_pos N

theorem toSpacingFunction_tends_zero (scheme : PhysicalLatticeScheme N_c) :
    Tendsto scheme.toSpacingFunction atTop (𝓝 0) :=
  scheme.ha_tends_zero

end PhysicalLatticeScheme

/-! ### Genuine continuum mass gap -/

/-- **Genuine continuum mass gap.**

A lattice mass profile `m_lat` exhibits a genuine continuum mass
gap with respect to a `PhysicalLatticeScheme` if the
**renormalized mass** `m_lat(N) / scheme.a(N)` converges to a
strictly positive limit `m_phys` as `N → ∞`.

This is in contrast to the existing `HasContinuumMassGap`
(in `ContinuumLimit.lean`) which uses `latticeSpacing N = 1/(N+1)`
and is satisfied by the coordinated `constantMassProfile m N`
artifact. -/
def HasContinuumMassGap_Genuine
    (scheme : PhysicalLatticeScheme N_c)
    (m_lat : LatticeMassProfile) : Prop :=
  ∃ m_phys : ℝ, 0 < m_phys ∧
    Tendsto (fun N => m_lat N / scheme.a N) atTop (𝓝 m_phys)

/-- Positivity follows by definition. -/
theorem HasContinuumMassGap_Genuine.pos
    {scheme : PhysicalLatticeScheme N_c} {m_lat : LatticeMassProfile}
    (h : HasContinuumMassGap_Genuine scheme m_lat) :
    ∃ m : ℝ, 0 < m := by
  obtain ⟨m_phys, hm_pos, _⟩ := h
  exact ⟨m_phys, hm_pos⟩

/-! ### The strict separation from existing predicate -/

/-
**Removed**: `hasContinuumMassGap_existing_of_genuine_aux`
(structural orphan, see Finding 004).

The genuine continuum mass gap (this file) does NOT imply the
existing `HasContinuumMassGap` (in `ContinuumLimit.lean`), because
the existing predicate uses a hard-coded `latticeSpacing N = 1/(N+1)`
while the genuine version uses an arbitrary `scheme.a`. The two
spacings need not agree, so the implication fails in general.

The "right fix" is to generalise the existing predicate to take a
spacing-function parameter. That refactor is left to a future
maintenance pass; for now the genuine and existing predicates are
treated as parallel rather than nested.

**Status**: theorem deleted (was sorry-ed, no downstream consumer).
The genuine predicate stands on its own; consumers should use
`HasContinuumMassGap_Genuine` directly via this file or
`DimensionalTransmutation.lean`.
-/

/-! ### Genuine Clay-grade predicate -/

variable {d : ℕ} [NeZero d] {G : Type*} [Group G] [MeasurableSpace G]

/-- **Genuine Clay-Yang-Mills physical-strong predicate.**

This is the predicate that any external Clay-grade announcement
should use, not the existing `ClayYangMillsPhysicalStrong` which
satisfies the continuum half via the coordinated-scaling artifact.

Combines:
- `IsYangMillsMassProfile m_lat` (genuine: requires the mass
  profile to actually bound Wilson connected correlators)
- `HasContinuumMassGap_Genuine scheme m_lat` (genuine: requires
  convergence of `m_lat(N) / scheme.a(N)` for a physical scheme,
  not the coordinated artifact). -/
def ClayYangMillsPhysicalStrong_Genuine
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (scheme : PhysicalLatticeScheme N_c) : Prop :=
  ∃ m_lat : LatticeMassProfile,
    IsYangMillsMassProfile μ plaquetteEnergy β F distP m_lat ∧
    HasContinuumMassGap_Genuine scheme m_lat

/-! ### Witness obligations (relocated) -/

/-
The two existence theorems

  `dimensional_transmutation_witness`
  `clayYangMillsPhysicalStrong_Genuine_witness`

have been **moved out of this file** to break a circular-import
problem.

They now live in
  `YangMills/L7_Continuum/PhysicalSchemeWitness.lean`
which imports both this file and `DimensionalTransmutation.lean`
and provides:

  * `dimensional_transmutation_witness_unconditional`:
    fully proven (no `sorry`), constructs a concrete
    `trivialPhysicalScheme` + `canonicalAFShape` witness.
  * `clayYangMillsPhysicalStrong_Genuine_witness`:
    proven modulo the `F3_chain_produces_AFTransmutating_shape`
    hypothesis (Branch II territory).

This file therefore contains **only structural definitions** of
`PhysicalLatticeScheme` and the genuine continuum-mass-gap
predicate. The witness work is downstream.

**Status**: this file is now `sorry`-free.
-/

end YangMills.Continuum
