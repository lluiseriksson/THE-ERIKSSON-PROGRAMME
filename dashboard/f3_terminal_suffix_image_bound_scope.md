# F3 residual canonical terminal-suffix image theorem scope (v2.141)

Task: `CODEX-F3-TERMINAL-SUFFIX-IMAGE-BOUND-SCOPE-001`

## Result

Scoped the next Lean-stable target behind the v2.140 blocker:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296
```

The intended bridge target is:

```lean
physicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296_of_residualFiberCanonicalTerminalSuffixImageBound1296
```

with conclusion:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296
```

No Lean file was edited in this scope pass.

## Proposed structure

The new target should be strictly sharper than
`PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296`.
It should split the v2.139 producer obligation into explicit residual-local
terminal-suffix data plus a selected-image bound.

The scope suggests a data object along the following lines:

```lean
structure PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData
    {L : ℕ} [NeZero L]
    (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (p : ConcretePlaquette physicalClayDimension L) where
  target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual}
  target_eq : target.1 = p
  source : {s : ConcretePlaquette physicalClayDimension L // s ∈ residual}
  canonicalWalk :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      source target
  terminalPred : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
  terminalSuffix :
    ((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
      terminalPred target
  terminalSuffix_is_last_edge :
    residual.card ≠ 1 →
      p ∈ (plaquetteGraph physicalClayDimension L).neighborFinset terminalPred.1
  suffix_source_from_canonical :
    -- evidence that `terminalSuffix` is extracted from `canonicalWalk`,
    -- not chosen independently or from deleted-vertex adjacency
    True
  terminalCode : Fin 1296
```

The placeholder above is schematic only. In Lean, the
`suffix_source_from_canonical` field should use whichever existing walk/path
relation is most stable locally: a suffix relation, a decomposition of
`canonicalWalk` into a prefix followed by the terminal edge, or a path-code
equality. The important requirement is that `terminalPred` is exposed as the
immediate predecessor extracted from residual-local canonical path/walk data.

The proposition should then quantify over the same v2.121 bookkeeping data as
v2.139:

- `root`, `k`;
- `deleted`, `parentOf`, and `essential`;
- the safe/low-cardinality bookkeeping choice clause;
- the essential image/fiber identity clause;
- `essential residual ⊆ residual`.

For each residual and each `p ∈ essential residual`, it should provide
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData residual p`.
Separately, over each residual, it should prove:

```lean
((essential residual).attach.image
  (fun p => (terminalSuffixData residual p).terminalPred.1)).card ≤ 1296
```

An equivalent injective `Fin 1296` code for the selected image is also acceptable
if the bridge can derive the card bound without adding an axiom.

## Bridge into v2.139

The bridge should be projection-only:

```lean
theorem physicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296_of_residualFiberCanonicalTerminalSuffixImageBound1296
    (hsuffix :
      PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296) :
    PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296 := ...
```

It should build `PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeData`
by copying:

- `target` and `target_eq`;
- `source` into `walkSource`;
- `canonicalWalk`;
- `terminalPred`;
- `terminalSuffix`;
- `terminalCode`.

It should discharge the v2.139 terminal-edge adjacency field from
`terminalSuffix_is_last_edge`, and carry over the selected-image cardinality
bound directly.

## Why this is sharper than v2.139

The v2.139 interface already asks for full walk terminal-edge data and a selected
image bound. The new target separates the missing proof burden into:

- a residual-local source of canonical walk/path data;
- an explicit statement that the terminal suffix is extracted from that canonical
  data;
- the final-edge adjacency proof inside the residual;
- the selected terminal-predecessor image bound.

This makes the future proof obligation auditable: a theorem that only proves
reachability or only packs a bounded menu will visibly fail to supply the
terminal-suffix extraction and selected-image clauses.

## Non-confusions

This target is not path existence. A path to `p` does not bound the image of the
immediate terminal predecessors selected over the residual fiber.

It is not root/root-shell reachability. First-shell data can start a route to
`p`, but it is not the terminal predecessor adjacent to `p`.

It is not a local-degree bound for one fixed plaquette, a residual-size bound, or
a raw residual-frontier bound. The bound is on the selected terminal-predecessor
image over the fiber.

It is not the v2.124 packing theorem. Packing can encode an already bounded menu;
it does not construct the residual-local terminal suffixes or prove the selected
image is bounded.

Deleted-vertex adjacency outside the residual must not be used as terminal
predecessor data, and terminal predecessors must not be chosen post-hoc from a
current `(X, deleted X)` witness.

## Validation

Dashboard-only scope artifact created. No Lean file was edited, so
`lake build YangMills.ClayCore.LatticeAnimalCount` was not required for this
scope step. The prior v2.140 attempt recorded a passing build for the current
Lean state.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Next task

Add the no-sorry Lean interface and, if safe, the projection bridge:

```text
CODEX-F3-TERMINAL-SUFFIX-IMAGE-BOUND-INTERFACE-001
```
