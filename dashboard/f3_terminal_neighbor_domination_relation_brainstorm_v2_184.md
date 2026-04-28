# F3 residual terminal-neighbor domination relation — Cowork creative brainstorm (post-v2.183)

**Task:** `COWORK-F3-CREATIVE-TERMINAL-NEIGHBOR-DOMINATION-RELATION-BRAINSTORM-001`
**Filed:** 2026-04-27T22:55:00Z
**Status:** brainstorm-only — no Lean theorem moved, no F3-COUNT status moved, no percentage moved.
**Companion to:**
- `dashboard/f3_absolute_selected_value_code_brainstorm_v2_167.md` (v2.167 brainstorm — selected-value layer)
- `dashboard/f3_ambient_value_code_brainstorm_v2_174.md` (v2.174 brainstorm — ambient-value layer)

This is the third Cowork creative-research deliverable on the F3-COUNT chain, addressing the v2.183 sharpened blocker.

## Disclaimer

This is creative mathematical research, **not a status-moving proof claim**. F3-COUNT remains `CONDITIONAL_BRIDGE`. None of the strategies below has been formalized in Lean. Each strategy is a **candidate route** for the next Codex attempt at proving:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
```

—the upstream theorem that, per the v2.183 reduction, would supply `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296` directly. The reader should expect at most one of these candidates to survive a serious Lean attempt; the value of the brainstorm is in **isolating non-circular structural ideas** and **explicit falsification tests** for each route.

## Reminder of the v2.183 sharpened blocker

The v2.183 reduction landed:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominatingMenu1296
```

at `YangMills/ClayCore/LatticeAnimalCount.lean:4877`. The reduction projects, for each residual fiber and essential parent, the dominated terminal neighbor supplied by the existing dominating-menu relation. **The proof ignores the menu-cardinality field.** This means an upstream theorem need only supply the *domination relation part* — the structural selector — without proving any bounded menu.

The exact missing ingredient is therefore a residual-local **terminal-neighbor domination relation** that provides:

1. A residual terminal-neighbor candidate for every essential parent: `terminalNeighborOfParent : ∀ residual, EssentialParent residual → ResidualVertex residual`.
2. Membership of that candidate in the residual: `(terminalNeighborOfParent residual p).1 ∈ residual` (automatic from the subtype).
3. `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` for the selected candidate (the existing v2.121-aware selector-evidence record).

**Crucially**, this is *strictly weaker* than the v2.155 dominating-menu target because no cardinality bound on the menu (or on the selected image) is required.

## Why this is sharper than v2.155 (cardinality-free)

The v2.155 attempt failed because the dominating-menu construction required a bounded menu finset. The v2.183 reduction explicitly bypasses this — the selector source only needs the **domination-relation** field of `DominatingMenu1296`, which is a function + membership + selector evidence, with no cardinality requirement. **An upstream theorem that constructs only the relation can be much smaller** than one that also bounds the menu.

This brainstorm focuses on routes that produce *only* the relation and explicitly do not attempt menu cardinality.

## Rejected routes (recorded for honesty discipline)

The following are explicitly **NOT** acceptable per the dispatch:

- **Selected-image cardinality** (would re-introduce the v2.155 blocker).
- **Menu cardinality** (the v2.183 reduction explicitly bypasses this).
- `finsetCodeOfCardLe` on an already bounded selected image — circular.
- **Empirical / bounded-search evidence** in lieu of structural proof.
- The v2.161 reasoning cycle `SelectorImageBound → SelectorCodeSeparation → CodeSeparation → DominatingMenu → ImageCompression → SelectorImageBound`.
- **Post-hoc terminal-neighbor choice** from a current `(X, deleted X)` witness.
- **Local displacement codes**, **parent-relative** `terminalNeighborCode` equality (not separators).
- Local degree, residual size, raw frontier, residual paths alone, root-shell reachability alone, deleted-vertex adjacency alone (none of these are relations between essential parents and residual terminal neighbors).

## Three candidate strategies

### Strategy A — Canonical lex-minimal residual neighbor selector

**Intended invariant.** For each essential parent `p` in the residual fiber, define `terminalNeighborOfParent residual p` as the **lex-minimal** element of `(plaquetteGraph physicalClayDimension L).neighborFinset p.1 ∩ residual` under the canonical `Finset` enumeration on `ConcretePlaquette physicalClayDimension L`. Every essential parent has at least one residual neighbor by the existing v2.121 essential-subset-residual fact plus the residual being preconnected.

```lean
def terminalNeighborOfParent_strategyA
    {L : ℕ} (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}) :
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} :=
  let candidates := (plaquetteGraph physicalClayDimension L).neighborFinset p.1 ∩ residual
  -- nonempty by essential-residual-adjacency fact (TBD)
  ⟨candidates.min'_witness, candidates.min'_mem ⟩
```

with selector evidence given by the canonical `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` field constructed from the adjacency.

**Why non-circular.**
- Lex-minimality on a Finset is a **structural** operation, not a cardinality bound.
- The candidate set `(neighborFinset p.1) ∩ residual` is **always finite** by Mathlib `Finset` types — no need to bound it.
- The selector evidence uses **only** the v2.121 essential-residual-adjacency clause, not menu/image cardinality.
- Does NOT use `finsetCodeOfCardLe`, the v2.161 cycle, or any selected-image bound.

**First exact Lean upstream lemma to add.**

```lean
theorem essential_parent_has_residual_neighbor
    {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf : ...)
    (essential : ...)
    (residual : ...)
    (...v2.121 hypotheses...)
    (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}) :
    ((plaquetteGraph physicalClayDimension L).neighborFinset p.1 ∩ residual).Nonempty := by
  -- Should follow from v2.121 essential-subset-residual + residual being preconnected
  -- (preconnected anchored subsets have at least one neighbor relationship).
  sorry
```

**Falsification test.** *If the lemma can be proved using only the v2.121 essential clauses (essential ⊆ residual, image identity, anchored subset preconnected), then Strategy A closes.* If the proof requires post-hoc inspection of `(X, deleted X)` for the specific anchored subset, Strategy A collapses (forbidden post-hoc choice).

**Risk of circularity (low).** Lex-minimality + adjacency + preconnectedness are all v2.121-compatible upstream structures. The only risk is if `essential_parent_has_residual_neighbor` itself requires the dominating-menu bound (in which case the strategy is circular). The v2.121 essential-subset clause + preconnected fact should be sufficient without any cardinality bound.

**Codex effort estimate.** ~50-100 LOC + 2 lemmas (existence + selector-data extraction).

---

### Strategy B — Bookkeeping-aware deleted-vertex selector

**Intended invariant.** For each essential parent `p` in the residual fiber, use the v2.121 bookkeeping data to pick the deleted vertex `deleted X` from a canonical anchored subset `X` whose `parentOf X = p`. By the v2.121 essential-image identity, every essential parent has at least one such `X`. Pick the canonical (e.g., lex-minimal under Finset enumeration) such `X`, and define `terminalNeighborOfParent residual p := deleted X` (which is adjacent to `parentOf X = p` per v2.121's adjacency clause).

```lean
def terminalNeighborOfParent_strategyB
    {L : ℕ} (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}) :
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} :=
  let X_for_p := canonical_X_with_parentOf_eq_p p   -- via Classical.choose on essential-image identity
  ⟨deleted X_for_p, deleted_in_residual_proof X_for_p⟩
```

**Why non-circular.**
- The v2.121 essential-image identity is **already proved**: `essential residual = (anchored_subsets.filter (fun X => X.erase (deleted X) = residual)).image parentOf`.
- For each essential parent `p`, this identity guarantees at least one `X` with `parentOf X = p`.
- The "canonical" choice of `X` (e.g., lex-min via `Classical.choose` on the witness, or the structural `Finset.min'` on the filtered subset) is a structural selector, not cardinality.
- The adjacency `deleted X ∈ neighborFinset (parentOf X)` is already in v2.121's hypothesis (the high-cardinality branch clause).

**Wait — possible issue.** The v2.121 `deleted X ∈ X` (deleted lies in the original anchored subset, **not necessarily in the residual** `X.erase (deleted X)`). This is a serious objection: the deleted vertex is removed FROM the residual, so `deleted X ∈ residual` is FALSE.

So Strategy B as stated is **broken** — the deleted vertex is not in the residual. We need to pick a *different* vertex as the terminal neighbor.

**Repaired Strategy B.** Use `parentOf X` itself as the terminal neighbor candidate? But `parentOf X` is the essential parent, not a different vertex. Instead, pick a residual neighbor of `parentOf X` other than the deleted vertex. This requires:

```lean
def terminalNeighborOfParent_strategyB_repaired
    {L : ℕ} (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}) :
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} :=
  let X_for_p := canonical_X_with_parentOf_eq_p p
  -- Pick a residual neighbor of p.1 other than deleted X_for_p
  let candidates := (neighborFinset p.1) ∩ residual
  ⟨candidates.min'_witness, _⟩  -- collapses into Strategy A
```

So **Strategy B collapses into Strategy A** when repaired correctly. The v2.121 bookkeeping does not give us a *different* terminal neighbor than what Strategy A's lex-minimal residual neighbor gives us.

**Falsification test.** *If we cannot exhibit a residual neighbor of `parentOf X` that is structurally different from the lex-minimal choice in Strategy A, then Strategy B is redundant.* Likely outcome: Strategy B is **redundant** with Strategy A.

**Risk of circularity (high — and worse: redundant).** Strategy B as initially stated picks a vertex not in residual (deleted X). The repair collapses into Strategy A. **Strategy B should be deprioritized in favor of Strategy A.**

**Codex effort estimate.** N/A — Strategy B is redundant with Strategy A.

---

### Strategy C — Canonical-last-edge walk-based selector (v2.131-v2.137 framework)

**Intended invariant.** Use the canonical-last-edge framework (v2.131-v2.137) to construct a deterministic walk from the anchored root to each essential parent. The **last edge** of this walk produces a residual terminal neighbor by construction. Specifically:

1. For each essential parent `p`, take the canonical-last-edge walk `w_p` from root to `p.1` in the residual subgraph.
2. The penultimate vertex of `w_p` is a residual neighbor of `p.1`.
3. Define `terminalNeighborOfParent residual p := penultimate_vertex(w_p)`.

```lean
def terminalNeighborOfParent_strategyC
    {L : ℕ} (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual}) :
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} :=
  let walk := canonical_last_edge_walk_residual root p.1 residual
  ⟨walk.penultimate_vertex, penultimate_vertex_in_residual_proof walk⟩
```

with selector evidence from the canonical-last-edge bound (already proved in v2.131-v2.137 framework).

**Why non-circular.**
- The canonical-last-edge walk is a **structural** construction from the residual subgraph topology, not a cardinality bound.
- The v2.131-v2.137 framework already has bounded-image lemmas for canonical-last-edge endpoints, but **we don't need that bound here** — we only need the walk's existence and the penultimate vertex's residue.
- Does NOT use selected-image cardinality, finsetCodeOfCardLe, or the v2.161 cycle.

**First exact Lean upstream lemma to add.**

```lean
theorem canonical_last_edge_walk_penultimate_in_residual
    {L : ℕ} [NeZero L]
    (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (root : ConcretePlaquette physicalClayDimension L)
    (p : {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual})
    (preconnected : preconnected_property residual)
    (root_in_residual : root ∈ residual) :
    ∃ q : ConcretePlaquette physicalClayDimension L,
      q ∈ residual ∧ q ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p.1 := by
  -- Should follow from existence of a walk in residual + finiteness
  sorry
```

**Falsification test.** *If `root_in_residual` is FALSE for some residual fiber, Strategy C collapses.* Need to verify: per v2.121 anchored bookkeeping, is the root always in the residual? **Likely not** — the residual is the result of erasing the deleted vertex, not necessarily containing the root. If the root is ONLY in the original anchored subset and not necessarily in the residual, Strategy C requires a different walk source (e.g., from the essential parent itself walking outward), which collapses into Strategy A.

**Risk of circularity (medium — and likely redundant with A).** The canonical-last-edge framework was originally introduced for the v2.131-v2.134 bounded-image proofs; its bounded-image lemmas would re-introduce cardinality routes. To use it here cardinality-free, we'd need only the walk's *existence* — which is exactly the preconnected-residual + adjacency fact that Strategy A uses. **Strategy C therefore likely collapses into Strategy A** with extra LOC.

**Codex effort estimate.** ~150-300 LOC + 3-4 lemmas; ROI is poor relative to Strategy A.

---

## Tradeoff comparison

| Aspect | Strategy A | Strategy B | Strategy C |
|---|---|---|---|
| Selector | lex-min residual neighbor | bookkeeping-aware (BROKEN; redundant) | canonical-last-edge penultimate (likely redundant with A) |
| Required upstream lemma | `essential_parent_has_residual_neighbor` (existence of residual neighbor) | (collapses into A) | `canonical_last_edge_walk_penultimate_in_residual` (existence; redundant with A) |
| Risk of circularity | Low | Broken (vertex not in residual) | Medium (likely redundant) |
| Codex effort estimate | ~50-100 LOC + 2 lemmas | redundant | ~150-300 LOC + 3-4 lemmas |
| Avoids menu/image cardinality? | ✓ | ✓ but redundant | ✓ but redundant |
| Strategic recommendation | **PRIMARY** | Skip | Fallback only if A fails |

**Recommended primary: Strategy A.** Lex-minimal residual neighbor + essential-residual-adjacency lemma. Strategies B and C either collapse or break.

## Falsification tests summary

| Test | Strategy A | Strategy B | Strategy C |
|---|---|---|---|
| Does `essential_parent_has_residual_neighbor` follow from v2.121 + preconnected? | If yes: closes | (N/A) | (would also close A) |
| Does `deleted X` lie in the residual? | (N/A) | NO — falsifies B | (N/A) |
| Does `root` always lie in the residual? | (N/A) | (N/A) | unclear; falsifies C if no |
| Does the route use selected-image or menu cardinality? | NO | NO | NO |
| Does the route use post-hoc choice from current witness? | NO (lex-min is canonical) | NO | NO |

## Distinguishes from rejected routes (verification table)

| Rejected route | How A avoids it |
|---|---|
| Selected-image cardinality | A defines selector by lex-min, never inspects cardinality |
| Menu cardinality | A produces the relation only; menu construction is downstream |
| `finsetCodeOfCardLe` on bounded image | A operates on (neighborFinset ∩ residual), not on bounded selected image |
| v2.161 cycle | A uses essential-residual-adjacency only; no selector-image bound, no code-separation, no dominating-menu cardinality |
| Local displacement codes | A uses absolute residual neighbor selection, not displacement |
| Parent-relative `terminalNeighborCode` | A's selector evidence is the canonical `SelectorData` record; no per-parent code equality across parents |
| Empirical / bounded search | A is structural lex-min, not empirical |
| Post-hoc terminal-neighbor choice | A's lex-min is **canonical** (depends only on residual + parent, not on a specific witness `X`) |

## Recommended next Codex follow-up

`CODEX-F3-TERMINAL-NEIGHBOR-DOMINATION-RELATION-INTERFACE-001` priority 5 — Codex adds the no-sorry Lean interface:

```lean
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296 : Prop := ...
```

with intended bridge:

```lean
theorem
  physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominationRelation1296
    (h : PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296
```

Then `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-DOMINATION-RELATION-001` priority 5 attempts Strategy A: prove the relation by constructing `terminalNeighborOfParent` via lex-min residual neighbor and supplying the selector evidence from `essential_parent_has_residual_neighbor`.

If Strategy A's first lemma `essential_parent_has_residual_neighbor` cannot be closed from v2.121 + preconnected alone, the proof attempt should record the exact missing structural ingredient as a Type D no-closure note, NOT use any of the rejected routes.

## Honesty preservation

- F3-COUNT row: unchanged (`CONDITIONAL_BRIDGE`).
- F3-MAYER, F3-COMBINED, OUT-* rows: unchanged (`BLOCKED`).
- All 4 percentages: unchanged at 5% / 28% / 23-25% / 50%.
- Tier-2 axiom count: unchanged at 4.
- Canonical 3-axiom trace: unchanged (`propext + Classical.choice + Quot.sound`).
- Vacuity caveats: unchanged (7 preserved verbatim).
- This document is a **brainstorm artifact**, NOT a proof. No theorem has been attempted in Lean, no Codex Lean file edited, no lake build run, no cardinality bound claimed, no LEDGER row moved.

## Cross-references

- `dashboard/f3_residual_fiber_terminal_neighbor_selector_source_attempt_v2_183.md` — v2.183 reduction note that motivates this brainstorm.
- `dashboard/f3_terminal_neighbor_dominating_menu_bound_attempt_v2_155.md` — v2.155 attempt that originally failed at menu cardinality.
- `dashboard/f3_baseaware_bookkeeping_proof_v2_121.md` — proved bookkeeping totalization (essential image identity, essential-residual-subset).
- `dashboard/f3_absolute_selected_value_code_brainstorm_v2_167.md` — Cowork brainstorm 1 (selected-value layer).
- `dashboard/f3_ambient_value_code_brainstorm_v2_174.md` — Cowork brainstorm 2 (ambient-value layer).
- `YangMills/ClayCore/LatticeAnimalCount.lean:4877` — v2.183 reduction theorem.
- `UNCONDITIONALITY_LEDGER.md` line 88 — F3-COUNT row evidence column (last cited at v2.169; AUDIT-021 filed REC-COWORK-LEDGER-EVIDENCE-COLUMN-EXTEND-002 priority 9 OPEN for the v2.170-v2.182 13-commit drift).
- `CLAY_HORIZON.md` appendix (vi) — pattern taxonomy showing the v2.161 cycle that all three strategies explicitly avoid.

---

*End of brainstorm. Filed by Cowork as deliverable for `COWORK-F3-CREATIVE-TERMINAL-NEIGHBOR-DOMINATION-RELATION-BRAINSTORM-001` per dispatcher instruction at 2026-04-27T22:55:00Z. **Third Cowork creative-research deliverable** on the F3-COUNT chain; companion to v2.167 brainstorm (selected-value layer; item 34) and v2.174 brainstorm (ambient-value layer; item 37). Strategies A/B/C analyzed with explicit falsification tests; honest recommendation: Strategy A (lex-min residual neighbor) is the only structurally non-redundant route; B is broken (deleted vertex not in residual); C likely collapses into A. 39th Cowork-authored deliverable (after v5 refresh = 38th). v5 deliverables-index does not yet list this brainstorm; AUDIT-008 result will be re-evaluated by next deliverables-consistency audit.*
