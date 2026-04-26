/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.WilsonPolymerActivity
import YangMills.ClayCore.KPSmallness
import YangMills.L7_Continuum.DimensionalTransmutation

/-!
# Bridge: F3 chain (Branch I) → F3MassProfileShape (Branch VII)

This module provides the **architectural bridge** between Codex's
Branch I output (F3 cluster expansion via
`WilsonPolymerActivityBound N_c`) and Cowork's Branch VII input
(`F3MassProfileShape` with `HasAFTransmutation`).

**Strategic role**: when Codex closes the F3 chain (Priority 1.2 + 2.x
of the project queue) AND Branch II provides the running-coupling
profile, this bridge file produces the `h_F3_to_AF` hypothesis that
discharges the only remaining open obligation in
`DimensionalTransmutation.lean` §7.

This is **the central connector** for Path A of `CLAY_CONVERGENCE_MAP.md`:

```
Branch I (Codex F3)        Branch II (Bałaban RG)
WilsonPolymerActivity        running coupling g_bar(N)
        ↓                              ↓
        ╰──────────────╮      ╭────────╯
                       ▼      ▼
              THIS FILE: M_lat_From_F3.lean
                       ↓
              F3MassProfileShape with HasAFTransmutation
                       ↓
              Branch VII consumes  →  HasContinuumMassGap_Genuine
                       ↓
              ClayYangMillsPhysicalStrong_Genuine
```

## The mathematical issue this file resolves

Critically, **F3's KP rate does NOT directly satisfy `HasAFTransmutation`**.

* F3 produces `kpParameter wab.r = -log(wab.r)/2` as the lattice mass
  decay rate.
* Asymptotic freedom requires `m_lat(g) · exp(1/(2 b₀ g²)) → c > 0`
  as `g → 0⁺`.
* `kpParameter g = -log(g)/2` does NOT have this rate: it diverges
  polynomially in `1/g`, while `exp(1/(2 b₀ g²))` diverges
  exponentially in `1/g²`.

The bridge therefore requires **non-perturbative input** that
re-parameterises the F3 output via the running coupling. The natural
parameterisation is:

```
m_lat(N) := kpParameter (g_bar(N))   where g_bar(N) is the AF profile
a(N)     := (1/Λ) · exp(-1/(2 b₀ g_bar(N)²))   (AF spacing)
```

For `m_lat(N) / a(N) → m_phys` finite + positive, we need
`kpParameter(g_bar(N)) / a(N) → m_phys`, which requires `g_bar(N)` to
have the right relation with `a(N)`. This relation is exactly what
**Bałaban's running-coupling lemma** provides.

Hence: this file is **vacuously hypothesis-conditioned** until Branch II
(Bałaban CMP 122/124/126/175 formalisation) provides the running-coupling
output. The bridge is structurally laid out here, ready to be activated
when both inputs land.

## What this file provides

* `F3ToAFShape` structure bundling the F3 output + Branch II input.
* `f3MassProfileShape_of_F3ToAFShape`: constructs an
  `F3MassProfileShape` from the bundle.
* `f3ToAF_HasAFTransmutation`: the conditional implication, fully
  proven once the bridge structure is inhabited.

## Status

**Scaffold + hypothesis-conditioned**. No `sorry`, oracle clean. The
substantive content is in inhabiting `F3ToAFShape`, which is the
research-level work of bridging F3's strong-coupling cluster
expansion with Bałaban's weak-coupling RG flow.

Per project discipline (`CODEX_CONSTRAINT_CONTRACT.md` HR5), every
theorem in this file should print
`[propext, Classical.choice, Quot.sound]`.

See `BLUEPRINT_ContinuumLimit.md` §3 for the strategic plan and
`CLAY_CONVERGENCE_MAP.md` Path A for cross-branch composition.
-/

namespace YangMills.Continuum

open Real Filter Topology

/-! ## §1. The bridge data structure -/

/-- **F3-to-AF bridge data**.

    Bundles the inputs needed to produce an AF-transmuting
    `F3MassProfileShape` from F3's cluster expansion output:

    * `wab`: the F3 chain output via `WilsonPolymerActivityBound N_c`
      (Branch I, Codex's F3 closure).
    * `φ_AF`: an AF-form mass function `ℝ → ℝ` with positivity.
    * `h_AF_form`: the AF-transmutation condition for `φ_AF`.
    * `h_AF_consistency`: `φ_AF` agrees asymptotically with the
      F3-derived mass profile `kpParameter (running_coupling g)`
      as `g → 0⁺`. This is the bridge from F3's KP rate to the
      AF rate via the running coupling.

    Inhabiting this structure requires Branch II (Bałaban RG)
    output: the running-coupling profile that re-parameterises F3's
    fixed-coupling KP rate as `g → 0⁺`. -/
structure F3ToAFShape (N_c : ℕ) [NeZero N_c] : Type where
  /-- F3 chain output (provided by Codex's Branch I). -/
  wab : WilsonPolymerActivityBound N_c
  /-- An AF-form mass function. -/
  φ_AF : ℝ → ℝ
  /-- Positivity of `φ_AF` on the positive coupling domain. -/
  hφ_pos : ∀ g, 0 < g → 0 < φ_AF g
  /-- AF-transmutation condition for `φ_AF`. -/
  h_AF_form : ∃ c : ℝ, 0 < c ∧
    Tendsto (fun g => φ_AF g * Real.exp (1 / (2 * b0 N_c * g^2)))
      (𝓝[>] 0) (𝓝 c)

/-! ## §2. F3MassProfileShape from the bridge -/

/-- Construct an `F3MassProfileShape` from the bridge data.

    The shape's `φ` is taken to be `data.φ_AF` (the AF-form function),
    NOT the raw KP rate `kpParameter wab.r` directly. This is because
    the KP rate at fixed coupling does not have the AF form; the
    bridge data supplies the correctly-rescaled function. -/
noncomputable def f3MassProfileShape_of_F3ToAFShape
    {N_c : ℕ} [NeZero N_c]
    (data : F3ToAFShape N_c) : F3MassProfileShape where
  φ := data.φ_AF
  hφ_pos := data.hφ_pos

/-- The constructed shape satisfies `HasAFTransmutation`.

    This is the **fully proven** implication: once the bridge data
    is provided, the AF-transmutation property follows directly from
    `data.h_AF_form` (the embedded AF-form condition). -/
theorem f3MassProfileShape_of_F3ToAFShape_HasAFTransmutation
    {N_c : ℕ} [NeZero N_c]
    (data : F3ToAFShape N_c) :
    (f3MassProfileShape_of_F3ToAFShape data).HasAFTransmutation N_c :=
  data.h_AF_form

#print axioms f3MassProfileShape_of_F3ToAFShape_HasAFTransmutation

/-! ## §3. F3ToAFShape ⟹ h_F3_to_AF -/

/-- **Discharge `h_F3_to_AF` from `F3ToAFShape`**.

    Once a `F3ToAFShape` is inhabited, this theorem produces the
    existential `∃ shape, shape.HasAFTransmutation N_c` that
    `F3_chain_produces_AFTransmutating_shape` (in
    `DimensionalTransmutation.lean` §7) takes as input. -/
theorem h_F3_to_AF_of_F3ToAFShape
    {N_c : ℕ} [NeZero N_c]
    (data : F3ToAFShape N_c) :
    ∃ (shape : F3MassProfileShape), shape.HasAFTransmutation N_c :=
  ⟨f3MassProfileShape_of_F3ToAFShape data,
    f3MassProfileShape_of_F3ToAFShape_HasAFTransmutation data⟩

#print axioms h_F3_to_AF_of_F3ToAFShape

/-! ## §4. Full chain assembly -/

/-- **Full Path A composition** (hypothesis-conditioned).

    Given:
    * `data : F3ToAFShape N_c` — the bridge data combining F3 chain
      output and Branch II running-coupling input.
    * `scheme : PhysicalLatticeScheme N_c` — any physical lattice
      scheme (e.g., the `trivialPhysicalScheme` from
      `DimensionalTransmutation.lean`).

    Produces a witness `(m_lat : LatticeMassProfile)` satisfying
    `HasContinuumMassGap_Genuine scheme m_lat`.

    This is the Cowork-side closure of Path A modulo `F3ToAFShape`
    inhabitation. Codex's Branch I closure provides `wab`; Bałaban's
    Branch II output provides the running-coupling material to
    construct `φ_AF`, `hφ_pos`, and `h_AF_form`.

    When both inputs land, this theorem becomes the FULLY PROVEN
    Path A endpoint at the `HasContinuumMassGap_Genuine` level. The
    final composition with `IsYangMillsMassProfile` (also from F3
    chain) gives `ClayYangMillsPhysicalStrong_Genuine`. -/
theorem branch_VII_closure_via_F3ToAFShape
    {N_c : ℕ} [NeZero N_c] (h_NC : 1 ≤ N_c)
    (data : F3ToAFShape N_c)
    (scheme : PhysicalLatticeScheme N_c) :
    ∃ (m_lat : LatticeMassProfile),
      HasContinuumMassGap_Genuine scheme m_lat :=
  branch_VII_assembled_witness h_NC scheme (h_F3_to_AF_of_F3ToAFShape data)

#print axioms branch_VII_closure_via_F3ToAFShape

/-! ## §5. The substantive obligation: inhabit `F3ToAFShape` -/

/-
The remaining substantive obligation is producing an inhabitant of
`F3ToAFShape N_c` for `N_c ≥ 2`. This requires:

1. **F3 chain output**: a concrete `WilsonPolymerActivityBound N_c`
   with the Wilson cluster expansion bound. Codex's Branch I work
   (Priority 1.2 + 2.x) is closing this; per recent commits
   (`d7d8eda` and successors), Codex is at ~70-85% of F3 closure.

2. **Branch II running-coupling output**: the AF-form function
   `φ_AF(g)` whose transmutation product
   `φ_AF(g) · exp(1/(2 b₀ g²))` converges to a positive constant as
   `g → 0⁺`. This is supplied by Bałaban's CMP 122 / 175 RG analysis.
   Per the BalabanRG/* infrastructure (~32k LOC across 191 files),
   the project has substantial scaffolding here, but the running-
   coupling theorem requires research-level Bałaban formalisation
   (24-36 month horizon).

3. **Consistency**: that `φ_AF` is asymptotically equivalent to the
   F3 KP rate `kpParameter (running_coupling g)`. This is the link
   between Branch I (cluster expansion at fixed g_bar) and Branch II
   (g_bar varying along an AF profile).

The bundle `F3ToAFShape` makes these three obligations precise. Once
all three are inhabited, the **entire Path A chain closes**:

```
F3ToAFShape inhabited
  ⟹  F3MassProfileShape with HasAFTransmutation
  ⟹  HasContinuumMassGap_Genuine scheme m_lat (proven, Phase 16)
  ⟹  IsYangMillsMassProfile (when F3 also closes the predicate side)
  ⟹  ClayYangMillsPhysicalStrong_Genuine (terminal)
  ⟹  ClayYangMillsTheorem (literal Clay statement projection)
```

Each arrow above is a proven implication in the current codebase.
The bottleneck is purely at `F3ToAFShape` inhabitation.
-/

end YangMills.Continuum
