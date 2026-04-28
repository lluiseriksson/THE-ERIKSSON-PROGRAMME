# F3 terminal-neighbor basepoint-independent code attempt v2.167

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-BASEPOINT-INDEPENDENT-CODE-001`

Target attempted: `PhysicalPlaquetteGraphResidualFiberTerminalNeighborBasepointIndependentCode1296`.

Result: no new Lean theorem was added. The current Lean interfaces and bridges build, but they do not provide the independent data needed to close the target without triggering the listed stop conditions.

## Exact no-closure blocker

The missing theorem is a residual-local absolute selected terminal-neighbor value-code construction for the v2.121 bookkeeping residual fibers:

- construct `terminalNeighborOfParent` on each essential parent in each residual fiber;
- provide `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` for each selected parent;
- construct an absolute/basepoint-independent code from the selected terminal-neighbor value image into `Fin 1296`;
- prove that this code is injective on selected terminal-neighbor values.

Existing ingredients expose local/per-witness selector data and downstream projection bridges, but they do not prove selected-value separation across different essential parents. In particular, local displacement codes or equality of a per-parent `terminalNeighborCode` field cannot be used as equality of selected terminal-neighbor values across different parent basepoints.

## Rejected routes

This attempt does not use `finsetCodeOfCardLe` on an already bounded selected image and does not route through the v2.161 circular chain

`SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation -> DominatingMenu -> ImageCompression -> SelectorImageBound`.

It also does not treat local degree, residual paths, root/root-shell reachability, residual size, raw frontier size, deleted-vertex adjacency, empirical search, packing/projection, or post-hoc terminal neighbors chosen from a current witness as proof of selected-image cardinality or selected-value separation.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed before this note was recorded. No Lean file was edited for v2.167, so there is no new theorem axiom trace to audit.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, ledger status, README badge, planner metric, or Clay-level claim moved.

## Next blocker-shaped task

A productive next theorem should isolate an independent absolute selected-value code producer, rather than another projection of existing bounded-image or menu interfaces. A plausible shape is a residual-local theorem that directly supplies the selected terminal-neighbor value image together with an injective `Fin 1296` code, with the code defined on absolute terminal-neighbor values rather than per-parent displacements.
