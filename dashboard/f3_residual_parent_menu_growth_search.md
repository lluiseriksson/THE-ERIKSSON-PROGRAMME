# F3 Residual Parent-Menu Growth Search

Timestamp: 2026-04-27T07:25:00Z

Task: `CODEX-F3-RESIDUAL-PARENT-MENU-GROWTH-SEARCH-001`

## Scope

This is a bounded diagnostic and hand-checking artifact. It is not a proof of
`PhysicalPlaquetteGraphResidualParentMenuBound1296`, and it is not used to move
`F3-COUNT`, any Clay-level percentage, or any project metric.

The search extends `scripts/f3_residual_parent_menu_bound_search.py` in two
directions:

1. The previous exact finite CSP search for a residual-menu assignment that
   chooses one admissible parent for each residual bucket in small physical
   models.
2. A new residual-local frontier-cover diagnostic: for a fixed residual bucket
   `R`, enumerate one-step extension vertices `z` with `R ∪ {z}` connected, and
   compute the least number of parents in `R` needed to cover all such extension
   vertices by adjacency.

The second diagnostic is intentionally stronger than the theorem needed by the
current F3 B.2 decoder route. It asks to cover every one-step extension of a
fixed residual, whereas the Lean target may only need a residual-only menu that
supports at least one safe deletion for each current anchored bucket. It is
useful as a growth detector, not as a formal refutation.

## Reproducible Run

Command:

```text
python scripts\f3_residual_parent_menu_bound_search.py
```

The script completed in about one second on the local checkout.

## Exact Menu CSP Results

The exact small-model CSP still found small menus:

| d | L | k | anchored buckets | residual variables | min menu size found |
|---:|---:|---:|---:|---:|---:|
| 2 | 2 | 2 | 2 | 1 | 1 |
| 2 | 2 | 3 | 3 | 2 | 2 |
| 2 | 3 | 3 | 5 | 2 | 2 |
| 3 | 2 | 3 | 109 | 11 | 2 |
| 4 | 1 | 3 | 10 | 5 | 1 |
| 4 | 2 | 3 | 838 | 29 | 2 |
| 2 | 3 | 4 | 11 | 5 | 2 |

This gives bounded no-growth evidence for the exact small cases tested. It does
not prove the universal `1296` bound.

## Residual-Local Frontier Diagnostic

The stronger residual-local diagnostic found linear growth in 2D strip-shaped
residuals:

| d | L | residual size | connected residuals checked | maximum cover found |
|---:|---:|---:|---:|---:|
| 2 | 3 | 2 | 2 | 2 |
| 2 | 3 | 3 | 5 | 3 |
| 2 | 4 | 4 | 13 | 4 |
| 3 | 2 | 3 | 109 | 3 |
| 3 | 2 | 4 | 8 capped | 2 |
| 4 | 2 | 3 | 838 | 3 |
| 4 | 2 | 4 | 8 capped | 2 |

The clearest hand-checkable pattern is the 2D row residual

```text
R_n = { (0,0), (0,1), ..., (0,n-1) }
```

with the same plaquette orientation. The one-step extensions above the row are

```text
z_i = (1,i), 0 <= i < n
```

and each `z_i` is adjacent only to the corresponding row parent `(0,i)` among
the listed row parents. Therefore covering all one-step extensions of `R_n`
requires at least `n` residual parents in this stronger diagnostic.

This is not by itself a counterexample to
`PhysicalPlaquetteGraphResidualParentMenuBound1296`, because the Lean target is
about safe-deletion support in the anchored decoder chain, not an unconditional
cover of every possible one-step extension of every residual. It does show that
any future proof must avoid confusing:

- local neighbor degree of one fixed parent,
- raw one-step frontier of a residual bucket,
- the essential safe-deletion parent frontier needed by the decoder.

## Current Conclusion

No counterexample needing more than `1296` parents was found in the exact small
CSP tested.

The stronger residual-local diagnostic shows that raw residual-frontier covers
can grow with residual size. Therefore the remaining theorem cannot be closed by
the already-available local degree bound alone.

The exact remaining formal target is still:

```text
PhysicalPlaquetteGraphResidualParentMenuBound1296
```

The structural lemma needed now should bound an essential safe-deletion parent
frontier, not the whole raw one-step extension frontier.

## Recommended Next Lean Target

Recommended next task: scope a stable sufficient lemma with a name like

```text
PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
```

Its intended shape:

```text
For every anchored current bucket X of card k, there is at least one safe
deletion z such that the parent needed to reconstruct z belongs to a
residual-only menu of size at most 1296 attached to X.erase z.
```

This lemma must be stronger than empirical search but weaker and more structured
than directly restating `PhysicalPlaquetteGraphResidualParentMenuBound1296`.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No Lean theorem, ledger row, or
percentage is upgraded by this search.
