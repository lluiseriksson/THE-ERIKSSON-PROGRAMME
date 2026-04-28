# F3 Decoder Symbol Strengthening Scope

Timestamp: 2026-04-27T04:25:00Z

Task: `CODEX-F3-DECODER-SYMBOL-STRENGTHENING-SCOPE-001`

## Status

This is a scope note only.  No Lean theorem is claimed closed, no
`UNCONDITIONALITY_LEDGER.md` status row is upgraded, and no Clay/lattice/planner
percentage moves.  `F3-COUNT` remains `CONDITIONAL_BRIDGE`.

The v2.72 result shows that the residual-extension compatibility theorem is
equivalent to the canonical residual-only parent selector:

```lean
physicalPlaquetteGraphResidualExtensionCompatibility1296_iff_canonicalResidualParentSelector1296
```

The finite search note
`dashboard/f3_residual_selector_counterexample_search.md` gives a physical
`d = 4, L = 2, k = 3` square-corner pattern showing why this residual-only
selector shape is too strong for the current decoder interface.

## Why `residual + Fin 1296` Is Insufficient

The current deleted-vertex contract is:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296
```

It asks for:

```lean
reconstruct :
  Finset (ConcretePlaquette physicalClayDimension L) ->
  Fin 1296 ->
  Option (ConcretePlaquette physicalClayDimension L)
```

The existing local inverse:

```lean
physicalNeighborDecodeOfStepCode
physicalNeighborDecodeOfStepCode_spec
```

is enough once a residual parent `p` is known.  The missing data is the choice of
which residual parent/frontier branch the local `Fin 1296` code should be read
relative to.

The square-corner pattern makes the issue concrete.  For residual `{r,a}`, one
anchored bucket forces parent `a`, while another bucket needs parent `r`.  A
function depending only on the residual cannot satisfy both.  The current
`Fin 1296` symbol only identifies a local neighbor after the parent is known; it
does not identify the parent/branch itself.

## Candidate Strengthenings

### Candidate A: Symbolic Parent Plus Local Neighbor Code

Alphabet:

```lean
Fin 1296 x Fin 1296
```

or, after packing if convenient:

```lean
Fin (1296 * 1296)
```

Interpretation:

- first component: a residual-frontier/parent selector code;
- second component: the existing local neighbor code decoded through
  `physicalNeighborDecodeOfStepCode`.

Proposed Lean identifiers:

```lean
PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296_of_symbolicResidualParentSelector1296
```

Migration path:

1. Keep v2.48-v2.72 definitions unchanged as the failed residual-only branch.
2. Add a parallel strengthened contract with a product symbol, not a replacement
   for `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296`.
3. Reuse `physicalNeighborDecodeOfStepCode_spec` for the second component.
4. Audit the changed alphabet size before any F3-COUNT or F3-MAYER constant is
   allowed to move.

Cost:

The alphabet is no longer 1296.  The direct bound becomes `1296^2 = 1679616`
unless a later compression proof recovers a smaller code.  That may affect the
Mayer/KP small-beta constants, so this is a closure route, not a status upgrade.

### Candidate B: Deterministic Deletion Rule With Residual Parent

Alphabet:

```lean
Fin 1296
```

Interpretation:

Change the deletion rule so that the residual alone determines a valid parent,
then continue using the existing local neighbor symbol.

Proposed Lean identifiers:

```lean
PhysicalPlaquetteGraphDeterministicResidualDeletionRule1296
physicalPlaquetteGraphDeletedVertexDecoderStep1296_of_deterministicResidualDeletionRule1296
```

Migration path:

This would preserve the old alphabet size, but it must overcome the square-corner
obstruction by proving that the chosen deletion order never needs the conflicting
residual assignments.  That is a substantially stronger global combinatorial
claim than the already-failed residual-only selector interface.

Cost:

High proof risk.  The current counterexample does not refute every deterministic
rule, but it shows that arbitrary safe deletion cannot be made residual-only
without extra structure.

### Candidate C: Global Deleted-Vertex Index

Alphabet:

```lean
Fin (Fintype.card (ConcretePlaquette physicalClayDimension L))
```

Interpretation:

Encode the deleted plaquette directly by a global finite enumeration.

Migration path:

This would trivially carry enough information, but the alphabet depends on the
volume parameter `L`, so it is not a uniform Klarner-style finite local alphabet.

Cost:

Reject for the F3 count route.  It avoids the local decoder problem by giving up
the uniform local alphabet needed downstream.

## Recommended Next Lean Target

Choose exactly one next target:

```lean
PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
```

The next Codex pass should add the interface and bridge only:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296_of_symbolicResidualParentSelector1296
```

This target is the smallest honest change because it preserves the existing
local neighbor-code machinery, explains the square-corner ambiguity, and avoids
pretending that a residual-only parent exists.  It also preserves the v2.48-v2.72
artifacts as useful no-closure evidence rather than invalidating them.

## Handoffs

New Codex-ready implementation task:

```text
CODEX-F3-SYMBOLIC-PARENT-SELECTOR-INTERFACE-001
```

The implementation should not move `F3-COUNT`.  At most it may land no-sorry
interfaces and bridge lemmas for the strengthened product-symbol decoder.  A
separate Cowork audit is required before any downstream constant or ledger text
can claim progress beyond `CONDITIONAL_BRIDGE`.
