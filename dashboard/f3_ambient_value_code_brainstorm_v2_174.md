# F3 ambient terminal-neighbor value code — Cowork creative brainstorm (post-v2.174)

**Task:** `COWORK-F3-CREATIVE-AMBIENT-VALUE-CODE-BRAINSTORM-001`
**Filed:** 2026-04-27T21:25:00Z
**Status:** brainstorm-only — no Lean theorem moved, no F3-COUNT status moved, no percentage moved.
**Companion to:** `dashboard/f3_absolute_selected_value_code_brainstorm_v2_167.md` (v2.167 brainstorm, which proposed the 3 origin tags now formalized in v2.173's `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin` inductive type).

## Disclaimer

This is creative mathematical research, **not a status-moving proof claim**. F3-COUNT remains `CONDITIONAL_BRIDGE`. None of the strategies below has been formalized in Lean. Each strategy is a **candidate route** for Codex's next attempt at proving:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296
```

—the v2.173 interface (`LatticeAnimalCount.lean:3900-3957`) whose first proof attempt (v2.174) returned `DONE_NO_CLOSURE_AMBIENT_BOOKKEEPING_VALUE_CODE_MISSING`. The reader should expect at most one of these candidates to survive a serious Lean attempt; the value of the brainstorm is in **isolating non-circular structural sub-lemmas** for each origin tag rather than in any one strategy being correct.

## Reminder of the no-closure blocker (verbatim from v2.174)

> The exact blocker is upstream of v2.173: the project has no ambient/base-zone/bookkeeping `Fin 1296` value code on residual vertices, and no theorem proving selected-value separation for terminal-neighbor values from such a code. The v2.121 bookkeeping theorem supplies `deleted`, `parentOf`, `essential`, and image/subset clauses, but it does not expose a base-zone enumeration, bookkeeping tag map into `Fin 1296`, or injectivity theorem on selected terminal-neighbor residual values.

So the v2.173 interface promises `ambientValueCode : {q // q ∈ residual} → Fin 1296` plus a selected-value separation clause, and its `ambientOrigin` field tags the upstream structural source. **No upstream theorem currently constructs any of the three origin-tagged codes.**

## Rejected routes (recorded for honesty discipline)

The following routes are explicitly **NOT** acceptable per the dispatch:

- `finsetCodeOfCardLe` on an already bounded selected image — circular.
- The v2.161 reasoning cycle `SelectorImageBound → SelectorCodeSeparation → CodeSeparation → DominatingMenu → ImageCompression → SelectorImageBound`.
- Local displacement codes; per-parent `terminalNeighborCode` equality.
- Local degree, residual paths, root/root-shell reachability, residual size, raw frontier size, deleted-vertex adjacency, empirical/bounded-search.
- Packing / projection of an already-bounded image onto itself.
- Choosing terminal neighbors **post-hoc** from a current witness.

## Three candidate strategies (matched to v2.173's three origin tags)

The v2.173 inductive `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin` defines three constructors: `baseZoneEnumeration`, `bookkeepingTag`, and `canonicalLastEdgeFrontier`. Each strategy below targets one origin and identifies the **first concrete Lean upstream lemma** that must be proved before the v2.173 interface can be discharged with that origin tag.

### Strategy A — `baseZoneEnumeration` origin: residual-fiber ⊆ base-zone enumeration

**Intended invariant.** Every residual-fiber vertex (not just selected terminal-neighbor values) lies in a fixed canonical 1296-coded ambient base zone. The base zone has a structural enumeration `baseZoneEnumeration : baseZoneVertices ↪ Fin 1296` that is independent of any selector, parent, or residual fiber. The ambient code is the composition: residual vertex → base-zone vertex → base-zone index. Selected-value separation is automatic from injectivity of the ambient code (distinct residual vertices receive distinct codes).

```lean
def ambientValueCode_strategyA
    {L : ℕ} (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) :
    Fin 1296 :=
  baseZoneEnumeration ⟨q.1, residual_subset_baseZone q.2⟩
```

with ambient-origin tag

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin.baseZoneEnumeration
```

**Why non-circular.**
- `baseZoneEnumeration` is given by the **construction** of the `1296`-bounded base zone (it is part of the ambient structure that every theorem in the chain is parameterized by, including the `1296` suffix on every theorem name).
- It does NOT depend on any selector, per-parent code, selected-image cardinality, or the v2.161 cycle.
- Injectivity is **automatic** from injectivity of `baseZoneEnumeration`.

**First exact Lean upstream lemma to add.**

```lean
theorem residualFiber_subset_baseZone
    {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf : Finset (ConcretePlaquette physicalClayDimension L) →
      ConcretePlaquette physicalClayDimension L)
    (essential : Finset (ConcretePlaquette physicalClayDimension L) →
      Finset (ConcretePlaquette physicalClayDimension L))
    (residual : Finset (ConcretePlaquette physicalClayDimension L))
    -- v2.121 bookkeeping hypotheses (same shape as v2.173)
    (...) :
    residual ⊆ baseZoneVertices := by
  -- Must follow from v2.121 bookkeeping locality + the fact that residual fibers
  -- arise from anchored-card enumeration over baseZoneVertices by construction.
  sorry
```

**Risk of circularity (low).** The base zone is **ambient** structure (it is the 1296-vertex region whose enumeration gives the `1296` suffix everywhere in the chain); the residual fiber is a sub-region of the base zone by `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard` membership. This is a structural corollary of v2.121 bookkeeping plus base-zone closure, NOT a downstream theorem. Codex must verify the lemma does not transitively appeal to a `SelectorImageBound`.

**Caveat.** This strategy assumes `baseZoneVertices` and `baseZoneEnumeration` already exist as ambient project structure. If they do not yet exist as a single Lean object — only as the implicit 1296 cardinality bound — Codex must first add a thin `def baseZoneVertices` plus `def baseZoneEnumeration` that satisfies the ambient axioms by construction.

---

### Strategy B — `bookkeepingTag` origin: v2.121 bookkeeping tag injection into Fin 1296

**Intended invariant.** The v2.121 bookkeeping totalization (`physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296` at `LatticeAnimalCount.lean:4809, 5836`) supplies, for each anchored subset `X`, a `(deleted X, parentOf X)` pair plus essential/image/subset clauses. Per residual fiber, this can be **lifted to a per-vertex tag** by composing the bookkeeping with a vertex-keyed projection: every vertex `q ∈ residual` is recoverable as the unique `parentOf X` for some `X` with `X.erase (deleted X) = residual`. The ambient code is the bookkeeping-tag-keyed enumeration into `Fin 1296`.

```lean
def ambientValueCode_strategyB
    {L : ℕ} (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) :
    Fin 1296 :=
  bookkeepingTagIntoFin1296 (bookkeepingTagOfResidualVertex residual q)
```

with ambient-origin tag

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin.bookkeepingTag
```

**Why non-circular.**
- The v2.121 bookkeeping is **already proved** (canonical 3-axiom trace `[propext, Classical.choice, Quot.sound]`).
- The tag-extraction operates on `(deleted, parentOf, essential)` data only; it does NOT need the selector.
- The 1296 bound on the tag domain is a corollary of the **base-zone cardinality bound**, NOT of the selector-image bound.

**First two exact Lean upstream lemmas to add.**

```lean
-- (1) Tag extractor: bookkeeping data → per-vertex tag
def bookkeepingTagOfResidualVertex
    {L : ℕ} (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) :
    BookkeepingTagSpace L :=
  -- Use v2.121 bookkeeping output for residual to extract a canonical tag for q.
  -- Candidate: the canonical (X, parentOf) pair witnessing q = parentOf X (via the
  -- image clause `essential residual = (... ).image parentOf` + Classical.choose
  -- on the witnessing X).
  sorry

-- (2) Tag domain has cardinality ≤ 1296
theorem bookkeepingTagSpace_card_le_1296
    {L : ℕ} : Fintype.card (BookkeepingTagSpace L) ≤ 1296 := by
  -- Must follow from the structural definition of BookkeepingTagSpace (e.g., it
  -- lives inside ConcretePlaquette physicalClayDimension L paired with a finite
  -- bookkeeping-direction enum). 1296 is the ambient base-zone constant.
  sorry

-- (3) Composite injection
def bookkeepingTagIntoFin1296 {L : ℕ} :
    BookkeepingTagSpace L ↪ Fin 1296 :=
  -- Combine (2) with `Fintype.card_le_iff_embedding` or a structural enumeration.
  sorry
```

**Risk of circularity (low-medium).** The hard step is proving `BookkeepingTagSpace` has cardinality ≤ 1296 **structurally** (from the ambient base-zone bound), not from selector-image cardinality. If `BookkeepingTagSpace` is defined as `ConcretePlaquette physicalClayDimension L` plus a finite direction enum, the bound follows from base-zone cardinality directly. **If** the bookkeeping-tag space is defined via the selected image, this strategy collapses. Codex must define `BookkeepingTagSpace` explicitly upstream of any selector data.

**Strategic note.** This is the strategy Codex's `CODEX-F3-TERMINAL-NEIGHBOR-AMBIENT-BOOKKEEPING-TAG-CODE-SCOPE-001` (the 21:10Z post-v2.174 next task) appears to target; this brainstorm gives the explicit first upstream lemmas to scope.

---

### Strategy C — `canonicalLastEdgeFrontier` origin: pairing canonical-last-edge endpoint with frontier-edge index

**Intended invariant.** Every residual-fiber vertex `q` is determined by a **pair**: (i) the canonical last-edge endpoint of `q`'s containing anchored subset `X` in the bookkeeping order (a vertex bounded into `Fin K1` by canonical-last-edge image lemmas v2.131-v2.134); (ii) the local frontier-edge index from that endpoint to `q` (bounded by `Fin K2` by graph-locality of `plaquetteGraph`). The ambient code is the **composition** of these two coordinates via a fixed pairing `Fin K1 × Fin K2 → Fin 1296` where `K1 * K2 ≤ 1296`.

```lean
def ambientValueCode_strategyC
    {L : ℕ} (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) :
    Fin 1296 :=
  pairingIntoFin1296
    (canonicalLastEdgeEndpointCode residual q)
    (frontierEdgeIndex residual q)
```

with ambient-origin tag

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin.canonicalLastEdgeFrontier
```

**Why non-circular.** Builds on **two already-proved** structural ingredients:
- `physicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296` (v2.131-v2.134) — canonical-last-edge image bounded into `Fin K1`.
- `plaquetteGraph` adjacency is locally bounded by graph-theoretic structure (each vertex has ≤ K2 neighbors in `physicalClayDimension = 4`), giving the frontier-edge index bound.

Does NOT use:
- the selector-image bound,
- `finsetCodeOfCardLe`,
- the v2.161 cycle (canonical-last-edge precedes selector-image in the bookkeeping order),
- post-hoc selection.

**First two exact Lean upstream lemmas to add.**

```lean
-- (1) Canonical-last-edge endpoint extraction (residual-vertex-keyed)
def canonicalLastEdgeEndpointCode
    {L : ℕ} (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) :
    Fin K1 :=
  -- Use v2.131-v2.134 canonical-last-edge image bound to extract the bounded
  -- last-edge endpoint code. Note: this is on ALL residual vertices, not just
  -- selected; the v2.131-v2.134 lemmas must be confirmed to apply to all
  -- residual vertices, not only selected terminal-neighbors.
  sorry

-- (2) Frontier-edge locality bound
theorem frontierEdge_locality_bound
    {L : ℕ} (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (endpoint : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}) :
    ((plaquetteGraph physicalClayDimension L).neighborFinset endpoint.1
      ∩ residual).card ≤ K2 := by
  -- Follows from local plaquette-graph adjacency in 4D (each plaquette has a
  -- structurally bounded number of neighbors in the same anchored region).
  sorry

-- (3) Pairing injection K1 × K2 → Fin 1296
def pairingIntoFin1296 {K1 K2 : ℕ} (h : K1 * K2 ≤ 1296)
    (a : Fin K1) (b : Fin K2) : Fin 1296 :=
  ⟨a.1 * K2 + b.1, by omega⟩  -- or similar structural pairing
```

**Risk of circularity (medium).** Step (1) — canonical-last-edge endpoint code on **all** residual vertices, not just selected — is a strict generalization of v2.131-v2.134, which only bound the canonical-last-edge image of the **selected** terminal-neighbor finset. If v2.131-v2.134 cannot be lifted to the full residual fiber without invoking a selector-image bound, this strategy collapses into the v2.161 cycle. Codex must verify v2.131-v2.134's hypotheses are actually structural (residual-fiber-keyed) and not selector-keyed.

**Strategic caveat.** Strategy C is structurally the most ambitious because it factors through *two* coordinates and requires lifting v2.131-v2.134's image bound from selected vertices to all residual vertices. If neither A nor B closes, C is the fallback; if A or B closes first, C remains valuable as an **independent verification path** (two non-circular routes to the same `Fin 1296` ambient code).

## Tradeoff comparison

| Aspect | Strategy A | Strategy B | Strategy C |
|---|---|---|---|
| Origin tag | `baseZoneEnumeration` | `bookkeepingTag` | `canonicalLastEdgeFrontier` |
| Code domain | base-zone enumeration of all base-zone vertices | bookkeeping tag space (residual-vertex → tag) | (last-edge endpoint, frontier-edge) pair |
| Injectivity source | base-zone enumeration injectivity | bookkeeping tag injectivity (corollary of v2.121) | pairing injectivity + step-1/step-2 locality |
| Required upstream lemma | `residual ⊆ baseZoneVertices` | `bookkeepingTagSpace_card_le_1296` + tag extractor | `frontierEdge_locality_bound` + canonical-last-edge lift to all residual vertices |
| Risk of circularity | Low — base zone is ambient | Low-medium — depends on tag domain definition | Medium — needs lift of v2.131-v2.134 from selected to all residual |
| Codex effort estimate | ~50-100 LOC + 1 lemma | ~100-150 LOC + 3 lemmas | ~200-300 LOC + 3 lemmas |
| Strategic fit | Best if base-zone enumeration exists ambient-side | Best if `BookkeepingTagSpace` is structurally definable upstream of selector | Best if Codex wants an independent verification path; or if A/B both fail |
| Selected-value separation | Automatic (injectivity of ambient code) | Automatic (injectivity of ambient code) | Automatic (injectivity of ambient code) |

All three strategies reduce v2.173's selected-value separation clause to **injectivity of the ambient code**, which is structurally simpler than the original separation requirement.

## Distinguishes from rejected routes (verification table)

| Rejected route | How A / B / C avoid it |
|---|---|
| `finsetCodeOfCardLe` on already-bounded selected image | A/B/C define the code on **all residual vertices**, not on the bounded selected image |
| v2.161 cycle | A uses base-zone (ambient, upstream of cycle); B uses v2.121 bookkeeping (already proved, upstream of cycle); C uses canonical-last-edge (v2.131-v2.134, upstream of selector-image) |
| Local displacement / per-parent terminalNeighborCode | A/B/C all use absolute (vertex-/tag-/coordinate-) codes on residual vertices, never parent-relative displacements |
| Residual paths / root-shell reachability | A/B/C define the code on residual vertices directly |
| Local degree / residual size / raw frontier size | A/B/C never use cardinality of residual fiber as input; only structural enumeration |
| Deleted-vertex adjacency | A/B/C operate on residual vertices, not on deletion-adjacency relations |
| Empirical / bounded-search | A/B/C are pure structural lemmas |
| Packing / projection of bounded image | A/B project from the **ambient** space; C builds a new pairing |
| Post-hoc terminal-neighbor choice | A/B/C define the code BEFORE the selector picks the terminal neighbor; the selected-value separation is then derived from injectivity of the pre-existing ambient code |

## Comparison with v2.167 brainstorm

The v2.167 brainstorm proposed Strategies A, B, C for the **selected-value** code (target: `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296`). Codex implemented the v2.170 absolute-selected-value interface and the v2.173 ambient interface, and the v2.173 inductive `AmbientCodeOrigin` formalized the 3 origins as enum constructors. **This brainstorm (v2.174) lifts v2.167's strategies one layer upstream**: from selected-value codes to the **ambient** value codes that supply them.

The structural insight is the same — code domain is ambient (base zone / bookkeeping tag / canonical-last-edge pairing), injectivity is structural — but the target is now the residual-vertex-keyed ambient code rather than the selected-vertex-keyed absolute code. The v2.173 bridge `physicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296_of_residualFiberTerminalNeighborAmbientValueCode1296` (lines 4039-4052) already converts ambient → selected, so closing v2.173 closes v2.170 by composition.

## Recommended next Codex follow-up

Codex's next dispatched task `CODEX-F3-TERMINAL-NEIGHBOR-AMBIENT-BOOKKEEPING-TAG-CODE-SCOPE-001` (21:10Z) targets **Strategy B**. This brainstorm supplies the 3 explicit first lemmas Codex should scope:

1. `bookkeepingTagOfResidualVertex` — tag extractor from v2.121 data
2. `bookkeepingTagSpace_card_le_1296` — structural cardinality bound
3. `bookkeepingTagIntoFin1296` — the composite injection

If Strategy B's first lemma fails on a Type D outcome (cardinality-bound circular through selector), Codex should fall back to **Strategy A** (more elementary base-zone projection; lower-risk because base zone is ambient structure). **Strategy C** remains as the third fallback or as an independent verification path after A or B closes.

A concrete follow-up Cowork task is recommended for the next META: `COWORK-AUDIT-CODEX-AMBIENT-BOOKKEEPING-TAG-SCOPE-001` (priority 4) — single-commit audit of whichever strategy Codex picks for the next attempt; Cowork verifies non-circularity, structural-vs-selector source for the cardinality bound, and Type-A/B/C/D classification of the outcome.

## Honesty preservation

- F3-COUNT row: unchanged (`CONDITIONAL_BRIDGE`).
- F3-MAYER, F3-COMBINED, OUT-* rows: unchanged (`BLOCKED`).
- All 4 percentages: unchanged at 5% / 28% / 23-25% / 50%.
- Tier-2 axiom count: unchanged at 4.
- Canonical 3-axiom trace: unchanged (`propext + Classical.choice + Quot.sound`).
- Vacuity caveats: unchanged (7 preserved verbatim).
- This document is a **brainstorm artifact**, NOT a proof. No theorem has been attempted in Lean, no Codex Lean file edited, no lake build run, no cardinality bound claimed, no LEDGER row moved.

## Cross-references

- `dashboard/f3_terminal_neighbor_ambient_value_code_interface_v2_173.md` — the v2.173 interface this brainstorm targets.
- `dashboard/f3_terminal_neighbor_ambient_value_code_attempt_v2_174.md` — the no-closure note that surfaced the missing ambient code.
- `dashboard/f3_terminal_neighbor_ambient_value_code_scope.md` — v2.172 scope (3 candidate origins).
- `dashboard/f3_absolute_selected_value_code_brainstorm_v2_167.md` — Cowork's prior brainstorm (downstream, selected-value layer).
- `dashboard/f3_baseaware_bookkeeping_proof_v2_121.md` — the proved totalization that Strategy B builds on.
- `YangMills/ClayCore/LatticeAnimalCount.lean:3878-3957` — v2.173 ambient-value-code interface declarations.
- `YangMills/ClayCore/LatticeAnimalCount.lean:4039-4052` — v2.173 ambient → absolute-selected projection bridge.
- `UNCONDITIONALITY_LEDGER.md` line 88 — F3-COUNT row evidence column (last cited at v2.169).
- `CLAY_HORIZON.md` appendix (vi) — pattern taxonomy showing the v2.161 cycle that all three strategies explicitly avoid.

---

*End of brainstorm. Filed by Cowork as deliverable for `COWORK-F3-CREATIVE-AMBIENT-VALUE-CODE-BRAINSTORM-001` per dispatcher instruction at 2026-04-27T21:25:00Z. Companion to v2.167 brainstorm; same structural framing lifted one layer upstream from selected-value to ambient-value codes. Strategies A, B, C are offered as candidate routes for Codex's next attempt; honest expectation is that Strategy B (currently dispatched as `CODEX-F3-TERMINAL-NEIGHBOR-AMBIENT-BOOKKEEPING-TAG-CODE-SCOPE-001`) is the most likely first close, with A as fallback and C as independent verification. 37th Cowork-authored deliverable (after deliverables-index v4 = 36th).*
