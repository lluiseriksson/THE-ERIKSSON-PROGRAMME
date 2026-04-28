# F3 residual bookkeeping tag value-code source scope v2.197

Task: `CODEX-F3-RESIDUAL-BOOKKEEPING-TAG-VALUE-CODE-SOURCE-SCOPE-001`

## Proposed theorem

Tentative Lean target:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296
```

This should be a structural residual-value code source for the v2.121
bookkeeping residual fibers.  It is upstream of:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296
```

and should supply the remaining explicit premise needed by the v2.182
two-premise bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296
```

## Required shape

Under the same v2.121 bookkeeping hypotheses used by
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296`, and
given a fixed residual-local selector

```lean
terminalNeighborOfParent :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
```

plus its selector evidence, the source theorem must provide:

```lean
∃ bookkeepingTagCode :
  ∀ residual,
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296,
  ∀ residual
    (p q : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}),
    bookkeepingTagCode residual (terminalNeighborOfParent residual p) =
      bookkeepingTagCode residual (terminalNeighborOfParent residual q) →
      (terminalNeighborOfParent residual p).1 =
        (terminalNeighborOfParent residual q).1
```

The crucial point is that the code lives on the whole residual subtype before
the terminal-neighbor image is considered.  The selected-value separation is a
restriction of this residual-value code to the selected terminal-neighbor
values.

## Exact bridge to add after the interface/source exists

The bridge target is:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296
```

Expected bridge name:

```lean
physicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296_of_residualFiberBookkeepingTagValueCodeSource1296
```

The bridge should be pure repacking: given the fixed
`terminalNeighborOfParent` and selector evidence required by
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296`, apply
the structural value-code source to obtain `bookkeepingTagCode` and its
selected-value separation.

## Candidate structural sources to inspect next

- Existing root-shell code lemmas such as
  `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellCode1296_injective`
  are genuine `Fin 1296` codes, but they code root-shell elements of an anchored
  bucket, not arbitrary residual subtype values.  They are therefore possible
  inspiration only, not a proof of the target.
- The v2.121 theorem
  `physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296` supplies
  `deleted`, `parentOf`, `essential`, residual image, and residual subset
  bookkeeping.  It does not itself supply a residual-value tag code.
- A viable proof must identify structural coordinates, base-zone tags, or
  bookkeeping tags that are already defined on each residual value and whose
  equality separates selected terminal-neighbor values.

## Explicit non-routes

This scope does not use or authorize:

- selected-image cardinality;
- bounded menu cardinality;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 cycle
  `SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation ->
   DominatingMenu -> ImageCompression -> SelectorImageBound`;
- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- empirical bounded search;
- residual size or raw frontier size;
- residual paths or root-shell reachability alone;
- deleted-vertex adjacency outside the residual;
- treating deleted `X` as a residual terminal neighbor for
  `residual = X.erase (deleted X)`.

## Validation

Dashboard-only scope.  No Lean file was edited, so no lake build is required for
this task.  The artifact names the bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296` and keeps
the residual-value tag-code burden separate from selected-image and
parent-relative-code routes.

F3-COUNT remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, vacuity caveat, proof claim, or Clay-level claim
moved.

## Next task

`CODEX-F3-RESIDUAL-BOOKKEEPING-TAG-VALUE-CODE-SOURCE-INTERFACE-001`

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagValueCodeSource1296` and, only
if it builds without sorry, the bridge into
`PhysicalPlaquetteGraphResidualFiberBookkeepingTagCodeForSelector1296`.
