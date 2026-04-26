/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.BalabanRG.UniformLSITransfer

/-!
# `ClayCoreLSI` — direct trivial inhabitant

This module proves that `ClayCoreLSI d N_c c` is **structurally
trivially inhabitable** for every `d`, `N_c`, and any `c > 0`,
without invoking Codex's `BalabanRGPackage` chain. The proof is
direct: take `beta0 := c`.

## Why `ClayCoreLSI` is not the log-Sobolev inequality

Despite its name, the definition in `UniformLSITransfer.lean` is:

```
def ClayCoreLSI (_d N_c : ℕ) [NeZero N_c] (c : ℝ) : Prop :=
  ∃ (beta0 : ℝ), 0 < beta0 ∧ 0 < c ∧ ∀ (β : ℝ), beta0 ≤ β → c ≤ β
```

This is **NOT** the integral form of the log-Sobolev inequality
`∫f²log(f²) - (∫f²)log(∫f²) ≤ (2/α) E f`. It is a purely arithmetic
existential: "there exists some threshold `beta0` past which `c ≤ β`".
For any `c > 0`, take `beta0 := c` — then for all `β ≥ c`, we have
`c ≤ β` by the hypothesis `beta0 ≤ β` (after substitution).

The actual log-Sobolev content of the project's Branch II chain is
encoded in `ClayCoreLSIToSUNDLRTransfer d N_c`
(`WeightedToPhysicalMassGapInterface.lean`), which transports from
`ClayCoreLSI` to the substantive `DLR_LSI` predicate (defined in
`LSIDefinitions.lean`).

This file makes explicit, in a single direct theorem, what is
structurally hidden in Codex's full BalabanRG chain.

## Implication for the project

Codex's `physical_uniform_lsi d N_c : ∃ c > 0, ClayCoreLSI d N_c c`
(in `PhysicalBalabanRGPackage.lean`) is *not* a proof of uniform
log-Sobolev for the Wilson Gibbs measure — it is a proof of an
arithmetic triviality. The substantive Branch II analytic content
lives entirely in:

* The **trivial-witness layer**: `physicalContractionRate := exp(-β)`,
  `physicalPoincareConstant := (N_c/4)·β`, etc., are placeholders
  to be upgraded with genuine RG dynamics.
* The **bridge structure** `ClayCoreLSIToSUNDLRTransfer`: still
  hypothesis-conditioned (its `transfer` field is the actual analytic
  obligation).

Documented as `COWORK_FINDINGS.md` Finding 016.

## Oracle target

`[propext, Classical.choice, Quot.sound]`.

-/

namespace YangMills.ClayCore

/-! ## §1. Direct trivial inhabitant -/

/-- **`ClayCoreLSI` is trivially inhabitable** for any positive `c`,
    by taking `beta0 := c`. -/
theorem clayCoreLSI_trivial
    (d N_c : ℕ) [NeZero N_c] (c : ℝ) (hc : 0 < c) :
    ClayCoreLSI d N_c c :=
  ⟨c, hc, hc, fun _ hβ => hβ⟩

#print axioms clayCoreLSI_trivial

/-! ## §2. Existential form -/

/-- **`∃ c > 0, ClayCoreLSI d N_c c` is trivially inhabited** for any
    `d, N_c`. Provides a one-line direct proof of Codex's
    `physical_uniform_lsi` conclusion, without going through the
    `BalabanRGPackage` chain. -/
theorem exists_clayCoreLSI_trivial (d N_c : ℕ) [NeZero N_c] :
    ∃ c > 0, ClayCoreLSI d N_c c :=
  ⟨1, one_pos, clayCoreLSI_trivial d N_c 1 one_pos⟩

#print axioms exists_clayCoreLSI_trivial

/-! ## §3. Coordination note -/

/-
This file isolates the structural-triviality of `ClayCoreLSI` for
explicit project documentation. Two parallel routes now exist for
inhabiting `∃ c > 0, ClayCoreLSI d N_c c`:

| Route | File | Mechanism |
|-------|------|-----------|
| Codex (Branch II chain) | `BalabanRG/PhysicalBalabanRGPackage.lean` | physicalRGRatesWitness → BalabanRGPackage → uniform_lsi_of_balaban_rg_package |
| Cowork (direct) | THIS FILE | `clayCoreLSI_trivial`: `⟨c, hc, hc, fun _ hβ => hβ⟩` |

Both routes are oracle-clean. Both produce the same conclusion. The
difference is depth: Codex's route has 30+ intermediate definitions
through the BalabanRG/ scaffolding; Cowork's route is a one-line
existential closure.

The fact that both routes reach the same conclusion confirms that
`ClayCoreLSI` is structurally vacuous as a stand-alone predicate.
The genuine analytic content of Branch II Bałaban-RG must live in
`ClayCoreLSIToSUNDLRTransfer` (the bridge to actual DLR-LSI), which
is currently a hypothesis-bearing structure.

Cross-references:
- `UniformLSITransfer.lean` — `ClayCoreLSI` definition.
- `WeightedToPhysicalMassGapInterface.lean` — `ClayCoreLSIToSUNDLRTransfer`,
  the actual analytic obligation carrier.
- `PhysicalBalabanRGPackage.lean` — Codex's chain to `physical_uniform_lsi`.
- `COWORK_FINDINGS.md` Findings 013, 014, 015, 016 — full
  structural-triviality analysis.
-/

end YangMills.ClayCore
