# F3 absolute selected terminal-neighbor value code — Cowork creative brainstorm (post-v2.167)

**Task:** `COWORK-F3-CREATIVE-ABSOLUTE-SELECTED-VALUE-CODE-BRAINSTORM-001`
**Filed:** 2026-04-27T12:30:00Z
**Status:** brainstorm-only — no Lean theorem moved, no F3-COUNT status moved, no percentage moved.

## Disclaimer

This is creative mathematical research, **not a status-moving proof claim**. F3-COUNT remains `CONDITIONAL_BRIDGE`. None of the strategies below has been formalized in Lean. Each strategy below is offered as a **candidate route** for Codex's next attempt at proving:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296
```

—the v2.166 interface whose first proof attempt (v2.167) returned `DONE_NO_CLOSURE_BASEPOINT_INDEPENDENT_CODE_MISSING`. The reader should expect at most one of these candidates to survive a serious Lean attempt; the value of the brainstorm is in **isolating non-circular structural ideas** rather than in any one strategy being correct.

## Reminder of the no-closure blocker (verbatim from v2.167)

The missing theorem is a residual-local absolute selected terminal-neighbor value-code construction over v2.121 bookkeeping residual fibers. It must:

1. Construct `terminalNeighborOfParent` on each essential parent in each residual fiber;
2. Provide `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` for each selected parent;
3. **Construct an absolute / basepoint-independent code from the selected terminal-neighbor value image into `Fin 1296`**;
4. **Prove the code is injective on selected terminal-neighbor values across different essential parents.**

Existing local displacement codes and per-parent `terminalNeighborCode` fields cannot serve because they only separate values **within a single parent's frame**. Two different essential parents picking the same vertex as terminal neighbor will, in general, have different per-parent codes, and two different parents picking different vertices may have the same per-parent code. **The code must be defined on the absolute value, not on the parent-relative displacement.**

## Rejected routes (recorded for honesty discipline)

The following routes are explicitly **NOT** acceptable per the dispatch:

- `finsetCodeOfCardLe` on an already bounded selected image — circular (assumes the cardinality bound we're trying to prove).
- The v2.161 reasoning cycle `SelectorImageBound → SelectorCodeSeparation → CodeSeparation → DominatingMenu → ImageCompression → SelectorImageBound`.
- Local degree, residual paths, root/root-shell reachability, residual size, raw frontier size, deleted-vertex adjacency.
- Empirical / bounded-search evidence in lieu of proof.
- Packing / projection of an already-bounded image onto itself.
- Choosing terminal neighbors **post-hoc** from a current witness.

## Three candidate strategies

### Strategy A — Fixed base-zone enumeration projection

**Intended invariant.** Every selected terminal-neighbor value lies in the bounded base zone (the structural region whose enumeration gives the `1296` suffix on every theorem name in the chain). The base zone has a *fixed canonical enumeration* `baseZoneIndex : BaseZoneVertex → Fin 1296`, independent of any selector or parent. The absolute code is the composition: selected value → base-zone vertex → base-zone index.

```lean
def absoluteSelectedValueCode_strategyA
    (sv : PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectedValue1296) :
    Fin 1296 :=
  baseZoneIndex sv.toBaseZoneVertex
```

**Why non-circular.** The base-zone enumeration is given by the **construction** of the `1296`-bounded base zone (it is part of the ambient structure that every theorem in the chain is parameterized by). It does NOT depend on:
- any selector (so cannot circularly require the selector-image bound),
- any per-parent code,
- the cardinality of the selected image,
- the v2.161 cycle.

Injectivity is **automatic** from injectivity of the base-zone enumeration: if two parents select vertices `v1 ≠ v2`, both in the base zone, then `baseZoneIndex v1 ≠ baseZoneIndex v2`.

**First exact blocker Codex should formalize.**
The non-trivial proof obligation is **selected values are in the base zone**:

```lean
theorem selected_terminal_neighbor_value_in_base_zone
    (residual : PhysicalPlaquetteGraphResidualFiber1296)
    (parent : EssentialParent residual)
    (sv : SelectedValue residual parent) :
    sv.toVertex ∈ baseZoneVertices := by
  -- Must follow from v2.121 bookkeeping locality + the residual fiber being a
  -- subset of the base zone by construction. The hard step is verifying that
  -- "essential parent" + "terminal neighbor of essential parent" preserves
  -- base-zone membership; this should be a corollary of the base-zone
  -- closure under the residual-graph adjacency relation.
  sorry
```

If this lemma can be established **without** routing through any cycle-component theorem (SelectorImageBound, SelectorCodeSeparation, CodeSeparation, DominatingMenu, ImageCompression), then Strategy A closes the target with code injectivity inherited from the base zone.

**Risk of circularity.** Codex must verify that "every essential parent in the v2.121 fiber has its terminal neighbor in the base zone" does NOT hide an appeal to an already-bounded selected-image lemma. The base zone is the **ambient** 1296-vertex region; the residual fiber is, structurally, a sub-region of the base zone (per v2.121 totalization), so this should be a structural corollary rather than a downstream theorem. Codex should write the lemma in terms of v2.121 totalization + base-zone membership only.

---

### Strategy B — Bookkeeping-tag absolute code via v2.120–v2.121

**Intended invariant.** The v2.121 bookkeeping totalization (`physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296`, proved via `physicalPlaquetteGraph_baseAwareLowCardBookkeepingTotalization1296` for `k ≤ 1` and a high-cardinality branch for `k ≥ 2`) assigns a **bookkeeping tag** to each vertex in the residual fiber. The selected terminal-neighbor value inherits its tag from the bookkeeping. The absolute code is the bookkeeping tag, encoded into `Fin 1296`.

```lean
def absoluteSelectedValueCode_strategyB
    (sv : PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectedValue1296) :
    Fin 1296 :=
  bookkeepingTagIntoFin1296 sv.toBookkeepingTag
```

**Why non-circular.** The bookkeeping tag is defined by `physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296`, which is **already proved** (v2.121). It does NOT depend on:
- the selector (the tag is a property of the residual fiber, not of any parent's choice),
- the selector-image cardinality (tags are tags regardless of how many distinct values appear),
- per-parent codes (tag is absolute),
- the v2.161 cycle (tag construction is upstream of every cycle-component theorem).

Injectivity follows from **bookkeeping tag injectivity**: distinct vertices in the residual fiber receive distinct tags, by the totalization clause.

**First exact blocker Codex should formalize.**
The non-trivial proof obligation is **bookkeeping tag injectivity into Fin 1296** for selected values:

```lean
theorem bookkeeping_tag_inject_into_fin1296_on_selected_values
    (residual : PhysicalPlaquetteGraphResidualFiber1296) :
    Function.Injective
      (fun (sv : SelectedValue residual) =>
         bookkeepingTagIntoFin1296 (sv.toBookkeepingTag))
:= by
  -- Key step: combine
  --   (i) tag-injectivity on residual-fiber vertices (corollary of v2.121
  --       totalization),
  --   (ii) cardinality of bookkeeping tags ≤ 1296 (corollary of base-zone
  --        cardinality bound, NOT of selector-image bound).
  -- The composition gives an injection from selected values to Fin 1296
  -- without invoking any cycle-component theorem.
  sorry
```

**Risk of circularity.** Codex must verify that the cardinality of bookkeeping tags ≤ 1296 is a property of the base zone alone, not derived from the selector-image bound. The `1296` constant in the bookkeeping is structural (it parameterizes the entire chain), so this should be a structural fact rather than a downstream theorem. **If** the bookkeeping tag domain is genuinely the same `Fin 1296` ambient space, this strategy is essentially equivalent to Strategy A but routed through bookkeeping rather than through base-zone enumeration. The two routes converge on the same structural fact: the absolute code domain is the ambient 1296-vertex region.

---

### Strategy C — Compositional code via canonical-last-edge + frontier-edge encoding

**Intended invariant.** Every selected terminal-neighbor value `v` at parent `p` is determined by a *pair*: (i) the canonical last-edge endpoint of `p` in the bookkeeping order (a vertex coded by v2.131-v2.134's canonical-last-edge image), and (ii) the local frontier edge from that endpoint to `v` (a bounded local choice). The absolute code is the **composition** of these two coordinates, encoded into `Fin 1296` via a fixed pairing function.

```lean
def absoluteSelectedValueCode_strategyC
    (sv : PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectedValue1296) :
    Fin 1296 :=
  pairingIntoFin1296
    (canonicalLastEdgeEndpointCode sv.parent)  -- from v2.131-v2.134
    (frontierEdgeIndex sv)                      -- bounded local choice
```

**Why non-circular.** Builds on **two already-proved** structural ingredients:
- `physicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296` (v2.131-v2.134) — the canonical last-edge image is bounded into Fin 1296.
- v2.121 bookkeeping totalization — the residual fiber has a finite, structurally-bounded set of vertices and edges.

Does NOT use:
- the selector-image bound (which is the downstream theorem we're trying to prove),
- `finsetCodeOfCardLe`,
- the v2.161 cycle (this route operates *upstream* of the cycle: canonical-last-edge precedes selector-image in the bookkeeping order).

**First exact blocker Codex should formalize.**
The non-trivial proof obligation is **injectivity of the pairing on selected values**:

```lean
theorem compositional_code_inject_on_selected_values
    (residual : PhysicalPlaquetteGraphResidualFiber1296) :
    Function.Injective
      (fun (sv : SelectedValue residual) =>
         pairingIntoFin1296
           (canonicalLastEdgeEndpointCode sv.parent)
           (frontierEdgeIndex sv))
:= by
  -- Key step: prove that (canonicalLastEdgeEndpointCode parent, frontierEdgeIndex sv)
  -- determines sv.toVertex uniquely.
  -- This requires:
  --   (A) for each fixed canonical-last-edge endpoint w, the map
  --       (parent → frontierEdgeIndex) → vertex is injective on parents
  --       sharing endpoint w (frontier edges leaving w have at most a bounded
  --       number of distinct targets in the residual fiber);
  --   (B) the pairing function pairingIntoFin1296 is injective.
  -- Step (A) is the genuinely new content; step (B) is structural.
  sorry
```

**Risk of circularity.** Step (A) — frontier-edge injectivity from a fixed canonical-last-edge endpoint — must be proved **without** invoking the selector-image bound or any cycle-component theorem. The most likely route: v2.121 bookkeeping gives, for each residual-fiber vertex `w`, a bounded number of frontier edges, each with a deterministic next-vertex assignment. This is a **structural locality** statement about the residual fiber, NOT a cardinality bound on the selected image.

The pairing function `pairingIntoFin1296` lives in `Fin (1296 / k) × Fin k → Fin 1296` for some structural `k` (e.g., the maximum frontier-edge degree of any residual-fiber vertex); choosing the right `k` is itself a structural problem.

**Caveat.** Strategy C is structurally the most ambitious: it factors the absolute code through *two* coordinates (last-edge + frontier-edge). If either coordinate's bound depends on the selector-image bound (transitively), this strategy collapses into the v2.161 cycle. Codex should verify upstream-only dependencies before committing to a Lean attempt.

## Tradeoff comparison

| Aspect | Strategy A | Strategy B | Strategy C |
|---|---|---|---|
| Code domain | base-zone enumeration | bookkeeping tag | (last-edge, frontier-edge) pair |
| Injectivity source | base-zone enumeration injectivity | bookkeeping tag injectivity (v2.121) | pairing injectivity + step-A locality |
| Required upstream lemma | selected values ⊆ base zone | tag domain ≤ 1296 | frontier-edge locality from fixed endpoint |
| Risk of circularity | Low — base zone is ambient structure | Low — v2.121 already proved | Medium — must verify two-coordinate bound is upstream of selector-image |
| Codex effort estimate | ~50-100 LOC + 1 lemma | ~80-120 LOC + 1 lemma | ~150-250 LOC + 2-3 lemmas |
| Strategic fit | Best if base-zone membership is a clean corollary of v2.121 | Best if bookkeeping tag is the "real" absolute identifier | Best if the chain ultimately needs explicit frontier-edge encoding for downstream theorems |

## Distinguishes from rejected routes (verification table)

| Rejected route | How each strategy avoids it |
|---|---|
| `finsetCodeOfCardLe` on already-bounded selected image | A/B/C all define the code on the **ambient** vertex space, not on the selected image |
| v2.161 cycle | A uses base-zone enumeration (upstream of cycle); B uses v2.121 bookkeeping (proved, upstream of cycle); C uses canonical-last-edge (v2.131-v2.134, upstream of selector-image) |
| Local displacement / per-parent terminalNeighborCode | A/B/C all use absolute (vertex- or tag- or coordinate-) codes, never parent-relative displacements |
| Residual paths / root-shell reachability | A/B/C define the code on selected values directly, without traversing residual paths |
| Local degree / residual size / raw frontier size | A/B/C never use the cardinality of the residual fiber as input; only its **structural enumeration** |
| Deleted-vertex adjacency | A/B/C operate on essential parents and their selected values, not on deletion-adjacency relations |
| Empirical / bounded-search | A/B/C are pure structural lemmas, no empirical input |
| Packing / projection of bounded image | A/B project from the **ambient** space, not from the bounded selected image; C builds a new pairing rather than projecting |
| Post-hoc terminal-neighbor choice from witness | A/B/C all define the code BEFORE the selector picks the terminal neighbor; the code is a function on absolute values, evaluated AFTER selection |

## Recommended next Codex follow-up

The seed-task `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-BASEPOINT-INDEPENDENT-CODE-001` (dispatched 11:58Z) is currently the active proof attempt. After v2.167's no-closure outcome, the natural next move is:

1. **Codex picks the strategy with the cleanest upstream-only dependency.** Strategy B is recommended as the lowest-risk first attempt because v2.121 bookkeeping totalization is **already proved** and the base-zone cardinality bound is structural (NOT downstream of selector-image).
2. **Codex formalizes the chosen strategy's first blocker as a separate scope-level theorem** before attempting the full target. For Strategy B, this means a new dashboard scope artifact `dashboard/f3_bookkeeping_tag_inject_into_fin1296_scope.md` followed by an interface task `CODEX-F3-BOOKKEEPING-TAG-INJ-INTERFACE-001`.
3. **If Strategy B's first blocker fails on a Type D outcome**, Codex falls back to Strategy A (more elementary base-zone projection) before attempting Strategy C (compositional, higher LOC).

A concrete follow-up Cowork task is added to the registry: `COWORK-AUDIT-CODEX-NEXT-BASEPOINT-INDEPENDENT-CODE-ATTEMPT-001` (priority 4) — single-commit audit of whichever strategy Codex picks for the next attempt; Cowork verifies non-circularity and Type-A/B/C/D classification of the outcome.

## Honesty preservation

- F3-COUNT row: unchanged (`CONDITIONAL_BRIDGE`).
- F3-MAYER, F3-COMBINED, OUT-* rows: unchanged (`BLOCKED`).
- All 4 percentages: unchanged at 5% / 28% / 23-25% / 50%.
- Tier-2 axiom count: unchanged at 4.
- Canonical 3-axiom trace: unchanged (`propext + Classical.choice + Quot.sound`).
- Vacuity caveats: unchanged (7 preserved verbatim).
- This document is a **brainstorm artifact**, NOT a proof. No theorem has been attempted in Lean, no Codex Lean file edited, no lake build run, no cardinality bound claimed, no LEDGER row moved.

## Cross-references

- `dashboard/f3_terminal_neighbor_basepoint_independent_code_interface_v2_166.md` — the interface scope this brainstorm is downstream of.
- `dashboard/f3_terminal_neighbor_basepoint_independent_code_attempt_v2_167.md` — the no-closure note that surfaced the missing absolute code.
- `dashboard/f3_baseaware_bookkeeping_proof_v2_121.md` — the proved totalization that Strategy B builds on.
- `UNCONDITIONALITY_LEDGER.md` line 88 — F3-COUNT row evidence column with full chain v2.48 → v2.166.
- `CLAY_HORIZON.md` appendix (vi) — pattern taxonomy showing the v2.161 cycle that all three strategies explicitly avoid.

---

*End of brainstorm. Filed by Cowork as deliverable for `COWORK-F3-CREATIVE-ABSOLUTE-SELECTED-VALUE-CODE-BRAINSTORM-001` per dispatcher instruction at 2026-04-27T12:30:00Z. This is the project's first creative-research deliverable specifically aimed at the absolute-selected-value-code blocker. Strategies A, B, C are offered as candidate routes for Codex's next attempt; honest expectation is that at most one survives a serious Lean attempt. 34th Cowork-authored deliverable (after CLAY_HORIZON v11 = 32nd, deliverables-index v3 refresh = 33rd).*
