# F3 residual terminal-neighbor image compression proof attempt (v2.152)

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-IMAGE-COMPRESSION-001`

## Result

Attempted to prove:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296
```

No Lean proof was added. The theorem cannot be closed from the current API
stack without either postulating a bounded residual terminal-neighbor menu or
using one of the explicitly forbidden substitutes.

## Exact No-Closure Blocker

The next missing ingredient is a residual-fiber terminal-neighbor dominating
menu theorem, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
```

It must construct, for every v2.121 bookkeeping residual fiber, a residual-local
finite menu

```lean
terminalNeighborMenu residual ⊆ residual
(terminalNeighborMenu residual).card ≤ 1296
```

and prove that every parent in `essential residual` has a residual-local
terminal neighbor in that menu, together with the same selector evidence needed
by `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`.

This is sharper than the v2.151 compression interface: v2.151 can project a
selector image into an already supplied bounded menu, but the current proof
obligation is to construct the bounded menu itself for each residual fiber.

## Existing APIs Checked

The current Lean APIs do not supply this menu:

* `plaquetteGraph_neighborFinset_card_le_physical_ternary` bounds the
  neighbors of one fixed plaquette, not the union or selected image over all
  parents in a residual fiber.
* residual path and induced-walk APIs give connectivity/path evidence but do
  not bound the terminal-neighbor image.
* root-shell and root-neighbor code APIs bound first-shell data from the root,
  not terminal neighbors adjacent to arbitrary essential parents.
* base-aware bookkeeping v2.121 constructs `deleted`, `parentOf`, and
  `essential`, but its available adjacency fact is for the deleted vertex
  outside the residual, not for a terminal neighbor inside the residual.
* v2.124/v2.151-style packing or projection theorems can code or use an
  already bounded menu, but do not construct the menu.

## Stop-Condition Check

Closing the theorem from the current ingredients would require one of the
forbidden moves:

* choosing terminal neighbors post-hoc from a current `(X, deleted X)` witness;
* using deleted-vertex adjacency outside the residual as terminal-neighbor data;
* treating local degree, residual path existence/splitting, root/root-shell
  reachability, residual size, raw frontier growth, empirical search, or packing
  as proof of selected-image cardinality.

Therefore the correct outcome is no closure and a sharper target.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

No new theorem was introduced, so no new theorem-specific axiom trace was
needed. The existing v2.151 bridge trace remains
`[propext, Classical.choice, Quot.sound]`.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Next Task

Scope the dominating-menu theorem:

```text
CODEX-F3-TERMINAL-NEIGHBOR-DOMINATING-MENU-SCOPE-001
```
