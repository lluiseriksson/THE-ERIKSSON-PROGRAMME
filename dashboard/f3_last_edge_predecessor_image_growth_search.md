# F3 last-edge predecessor image growth search v2.109

**Task:** `CODEX-F3-LAST-EDGE-PREDECESSOR-IMAGE-GROWTH-SEARCH-001`  
**Date:** 2026-04-27  
**Status:** `BOUNDED_NO_GROWTH_EVIDENCE_NO_PROOF`

## Artifact

Codex added the bounded diagnostic script:

```text
scripts/f3_last_edge_predecessor_image_growth_search.py
```

The script reuses the finite plaquette model from:

```text
scripts/f3_residual_selector_counterexample_search.py
```

That model is aligned with the Lean graph:

```lean
def plaquetteGraph (d L : Nat) [NeZero d] [NeZero L] :
    SimpleGraph (ConcretePlaquette d L) where
  Adj p q := p != q /\ siteLatticeDist p.site q.site <= 1
```

The Python diagnostic represents a concrete plaquette as `(site, direction)` and
uses the same non-loop adjacency threshold on base sites.

## What was measured

For a connected anchored residual bucket `R`, the script computes:

1. one-step extension vertices `z` such that `R ∪ {z}` is still anchored and
   connected;
2. the residual-only essential parent set
   `E(R) = {p in R | p is adjacent to at least one such z}`;
3. the least cardinality of a terminal-predecessor image `P ⊆ R` such that every
   `p ∈ E(R)` is adjacent to some `q ∈ P`.

This is deliberately not:

- the raw residual frontier,
- the cardinality of the residual,
- the local degree of one fixed portal,
- first-shell reachability from the root.

It is the finite-model analogue of the selected terminal-predecessor image that
blocks:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296
```

## Command

```bash
python scripts/f3_last_edge_predecessor_image_growth_search.py
```

## Bounded output summary

The default run checked exhaustive small cases and capped physical-dimension
cases:

| d | L | residual size | connected residuals checked | max minimum terminal-predecessor image |
|---|---|---:|---:|---:|
| 2 | 3 | 2 | 2 | 2 |
| 2 | 3 | 3 | 5 | 2 |
| 2 | 4 | 4 | 13 | 2 |
| 3 | 2 | 3 | 109 | 2 |
| 3 | 2 | 4 | 867 | 2 |
| 4 | 1 | 3 | 10 | 2 |
| 4 | 2 | 3 | 838 | 2 |
| 4 | 2 | 4 | 2500 capped | 2 |
| 4 | 2 | 5 | 2500 capped | 2 |

No tested case exhibited growth beyond `2`.

## Interpretation

This is bounded no-growth evidence only.  It does not prove
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`,
and it does not prove the selected-image bound by `1296`.

The search suggests that the next useful Lean target should not be another
decoder bridge.  It should isolate a structural last-edge domination statement:

```text
For every non-singleton connected anchored residual R, the residual-only
essential parent set E(R) admits a residual-local terminal-predecessor image
P ⊆ R, with |P| <= 1296, such that every p in E(R) is adjacent to some q in P.
```

To feed the v2.107 interface, that lemma must also supply a `Fin 1296`
separation code for the selected predecessor image.  The finite search gives no
permission to use empirical absence of counterexamples as proof.

## Next recommended task

```text
CODEX-F3-LAST-EDGE-DOMINATING-SET-LEMMA-SCOPE-001
```

Scope a Lean-stable residual essential-parent terminal-predecessor domination
lemma and its bridge into
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`.

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastStepPredecessorImageBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualLastStepPortalImageBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualPortalMenuBound1296`,
- `PhysicalPlaquetteGraphBaseAwareMultiPortalSupportedSafeDeletionOrientation1296x1296`,
- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296`,
- any compression to older constants,
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this task.
