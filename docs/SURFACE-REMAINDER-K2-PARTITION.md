# K2 head-subtracted partition contract

**Registered:** 2026-07-12, before any head-subtracted production run  
**Status:** design/pre-registration only; this document is not evidence of K2 or G2 closure

This contract fixes the birth partition and the admissible refinement rules for the
direct joint K2 judge.  Its purpose is to make a later green result falsifiable and to
prevent the mesh from being selected after inspecting the answer.

## Born delta partition

The endpoint lane is

```text
[0, 1/1000].
```

The positive lanes are

```text
[j/1000, (j+1)/1000],  j = 1,...,49,
```

and together cover `[0,1/20]`.  A failing born box may be bisected locally.  Every
descendant retains its born-box identifier and no later box may be widened or merged.

## Endpoint rule

The endpoint lane must use the regular `delta=0` identities.  Before interval
integration it subtracts the independently derived exact head

```text
T(c) + r2(c) delta + r3(c) delta^2.
```

Plain interval division by `delta` on a box containing zero is forbidden.  The fixed
completion contribution and the analytic outer tail are mandatory parts of the same
terminal budget; a localized core alone cannot pass.

## Ordered t partition

For each delta box the admissible physical range is

```text
0 < t <= pi - 1.5 delta.
```

Its born boxes have width `1/50`, with the final box clipped to the moving upper
boundary.  Local bisection is allowed, and descendants retain both their delta and t
birth identifiers.  A certificate must prove adjacency, non-overlap, and complete
coverage of this ordered domain.

## Terminal inequality and accounting

The registered direct inequality is unchanged from
`SURFACE-REMAINDER-S2-DIRECT-PREREG.md`.  The exact cubic head `r3` may be used for
internal centering, but its full contribution remains charged to the registered
`Theta3` budget.  Centering therefore cannot silently improve the theorem constant.

A terminal run must emit an immutable transcript and a run manifest containing the
executed script hash, dependency hashes, runtime versions, born and terminal box counts,
maximum depth, coverage verdict, every separate core/completion/tail budget, and the
final strict margin.  Until those artifacts validate, G2 remains open.
