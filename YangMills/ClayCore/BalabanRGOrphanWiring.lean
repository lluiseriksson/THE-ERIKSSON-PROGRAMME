/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cowork agent (Claude), under supervision of Lluis Eriksson
-/

/-!
# BalabanRG orphan wiring (Cowork Phase 68 audit follow-up)

This file is a **Cowork audit contribution** wiring the
high-keystone orphan files in `YangMills/ClayCore/BalabanRG/` into
the master import graph.

## Context

Codex's massive Branch II push (~222 files in `BalabanRG/`, see
`COWORK_FINDINGS.md` Finding 015) added 21 files that are not
imported transitively from `YangMills.lean`. Several of these
contain public-facing theorems with consolidation routes to
`ClayYangMillsTheorem` (counted by keystone-hits ≥ 1):

| Orphan file                                                          | Keystone hits | Notable theorem                      |
|----------------------------------------------------------------------|---------------|--------------------------------------|
| `BalabanRGAxiomReduction`                                            | 3             | `uniform_lsi_without_axioms`         |
| `P91FiniteFullSmallConstantsBudgetEnvelope`                          | 15            | small-constants envelope theorems    |
| `P91FiniteFullSmallConstantsLaneSymmetry`                            | 11            | lane-symmetry theorems               |
| `P91FiniteFullBridgeToDirectBudgetInterface`                         | 11            | direct-budget interface theorems     |
| `BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry`  | 9             | threshold-one equivalence registry   |
| `P91ExpSizeWeightLinearBudgetWitness`                                | 7             | exp-size-weight linear budget        |
| `HaarLSIConcreteBridge`                                              | 2             | concrete Haar-LSI bridge             |
| `E26EstimateIndex`                                                   | 1             | E26 estimate index                   |

## What this file does

It is a **single transparent re-export shim**: imports the high-
keystone orphans so that any consumer of this file (and therefore
of `YangMills.lean`, via the wiring) gains transitive access to
the public theorems in those files. This DOES NOT modify any of
Codex's files; it only wires them into the import graph at the
master level.

## Caveat

This is a Cowork audit contribution. Codex may have reasons to
keep certain files orphan (e.g., WIP, deliberately unwired,
deprecated routes). If Codex prefers a different wiring policy,
this file can be deleted without touching anything else.

## Oracle target

`[propext, Classical.choice, Quot.sound]` (transparent re-export).

-/

-- High-keystone orphans (per Phase 67 + 68 audit)
import YangMills.ClayCore.BalabanRG.BalabanRGAxiomReduction
import YangMills.ClayCore.BalabanRG.P91FiniteFullSmallConstantsBudgetEnvelope
import YangMills.ClayCore.BalabanRG.P91FiniteFullSmallConstantsLaneSymmetry
import YangMills.ClayCore.BalabanRG.P91FiniteFullBridgeToDirectBudgetInterface
import YangMills.ClayCore.BalabanRG.BalabanRGUniformLSIQuantitativeP81ThresholdOneEquivalenceRegistry
import YangMills.ClayCore.BalabanRG.P91ExpSizeWeightLinearBudgetWitness
import YangMills.ClayCore.BalabanRG.HaarLSIConcreteBridge
import YangMills.ClayCore.BalabanRG.E26EstimateIndex

namespace YangMills.ClayCore.BalabanRGOrphanWiring

/-! ## Coordination note

Phase 68 follow-up to Phase 67 audit. This file wires 8 of the 21
orphan files in `BalabanRG/` into the master import graph. The
remaining 13 orphans are either:

* Internal scaffolding with no keystone hits to `ClayYangMillsTheorem`
  (e.g., `BalabanFieldDecomposition`, `EntropyCouplingReduction`,
  `FiniteBlocks`).
* P91 window/staging files that may be intentionally orphaned WIP
  (e.g., `P91BetaDivergenceWindow`, `P91WindowClosed`,
  `P91RecursionDataWindow`).

If Codex audit confirms any remaining orphan should also be wired,
add it to the import list above.

Cross-references:
- `COWORK_FINDINGS.md` Finding 015 — full Codex BalabanRG/ push audit.
- `WeightedRouteClosesClay.lean` — primary `clayTheorem_of_*`
  consolidation routes.
- `BalabanRGAxiomReduction.lean` — `uniform_lsi_without_axioms`
  (the most prominent public theorem of the push).
-/

end YangMills.ClayCore.BalabanRGOrphanWiring
