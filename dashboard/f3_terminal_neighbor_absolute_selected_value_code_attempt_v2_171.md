# F3 terminal-neighbor absolute selected-value code attempt v2.171

Task: `CODEX-F3-PROVE-ABSOLUTE-SELECTED-VALUE-CODE-AFTER-INTERFACE-001`

Attempted target:

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296`

## Result

No Lean proof was added. The v2.170 interface and bridge are present and build,
so the previous v2.169 blocker (missing interface) is resolved. The remaining
blocker is now genuine mathematical content: the current Lean module has no
upstream theorem that constructs an absolute `Fin 1296` code on residual
selected terminal-neighbor values from the v2.121 bookkeeping residual fibers.

The target asks, for every v2.121 bookkeeping residual family, to construct:

- residual-local `terminalNeighborOfParent` selector data;
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` for each
  essential parent;
- an absolute residual-value code
  `{q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296`;
- selected-value separation: equal absolute codes on selected terminal-neighbor
  values force equality of those selected plaquettes across essential parents.

## Exact no-closure blocker

The next missing closure artifact is an upstream residual-local ambient-value
coding theorem, tentatively:

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`

It should be independent of the downstream terminal-neighbor cycle and should
supply a structural, absolute `Fin 1296` code for terminal-neighbor values in
each v2.121 bookkeeping residual fiber. A viable version may follow one of the
Cowork brainstorm routes:

- base-zone enumeration: prove every selected terminal-neighbor value lies in a
  fixed 1296-coded ambient/base zone and inherit injectivity there;
- bookkeeping-tag enumeration: prove the v2.121 bookkeeping tag of a selected
  terminal-neighbor value is absolute and injective into `Fin 1296`;
- canonical-last-edge/frontier-edge coordinates: prove an upstream coordinate
  pair determines the selected value and injects into `Fin 1296`.

Without one of these structural coding lemmas, proving
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296`
would require exactly the kind of new project axiom, `sorry`, empirical search,
or circular selected-image bound that the task forbids.

## Rejected routes

This attempt did not use local displacement codes, parent-relative
`terminalNeighborCode` equality, local degree, residual paths, root-shell
reachability, residual size, raw frontier, deleted-vertex adjacency, empirical
search, packing/projection, `finsetCodeOfCardLe` on an already bounded selected
image, the v2.161 circular chain, or post-hoc terminal neighbors chosen from a
current witness.

## Validation

- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- No Lean file was edited.
- No new theorem was added, so no new `#print axioms` trace is required.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, ledger status, README
  metric, planner metric, or Clay-level claim moved.

## Next Codex task

Scope or add the upstream structural-code interface for
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`, with
an explicit bridge into
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296`.
