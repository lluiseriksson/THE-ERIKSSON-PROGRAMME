# F3 residual terminal-neighbor dominating-menu proof attempt (v2.155)

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-DOMINATING-MENU-001`

## Result

Attempted to prove:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
```

No Lean proof was added.  The current API stack cannot construct the required
residual-indexed bounded menu without a new graph-theoretic separation theorem.

## Exact No-Closure Blocker

The next missing ingredient is a residual-fiber terminal-neighbor code
separation theorem, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296
```

It should construct, for each v2.121 bookkeeping residual fiber:

```lean
terminalNeighborOfParent :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}

terminalNeighborSelectorEvidence :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
        residual p.1 (terminalNeighborOfParent residual p)
```

together with a genuine selected-image separation proof, for example an
injective `Fin 1296` code on the selected terminal-neighbor image:

```lean
∀ residual,
  ((essential residual).attach.image
    (fun p => (terminalNeighborOfParent residual p).1)).card ≤ 1296
```

or an equivalent code/injectivity statement strong enough to derive this card
bound.  Then the dominating-menu theorem can take the selected image as
`terminalNeighborMenu` and use the selector evidence for domination.

This is sharper than `PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296`:
it isolates the missing mathematical burden as code separation for the selected
terminal neighbors, while the menu construction becomes `image
terminalNeighborOfParent`.

## APIs Checked

The current Lean APIs do not supply this separation:

* `plaquetteGraph_neighborFinset_card_le_physical_ternary` bounds the local
  neighbors of one fixed plaquette only.  The essential parents may range over a
  residual fiber, so this does not bound the union or a selected image.
* root-shell APIs and `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_*rootShell*`
  bound first-shell data from the anchored root, not terminal neighbors adjacent
  to arbitrary essential parents.
* residual path/reachability APIs can give walks or reachability evidence, but
  not an injective `Fin 1296` code on terminal-neighbor images.
* v2.121 base-aware bookkeeping supplies `deleted`, `parentOf`, `essential`,
  essential image identity, and essential subset residual.  Its adjacency fact
  concerns the deleted vertex outside the residual, not a terminal neighbor
  inside the residual.
* v2.154 projection can convert a bounded dominating menu into image
  compression, but it does not construct the menu.

## Stop-Condition Check

Closing the theorem from the current ingredients would require one of the
forbidden substitutions:

* choosing terminal neighbors post-hoc from a current `(X, deleted X)` witness;
* treating local degree, root-shell reachability, path existence, residual size,
  raw frontier growth, deleted-vertex adjacency, empirical search, or packing as
  proof of bounded-menu construction;
* merely repacking an already bounded menu.

Therefore the correct outcome is no closure and the sharper code-separation
target above.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

No new theorem was introduced by this attempt, so no new theorem-specific axiom
trace was needed.  The v2.154 bridge trace remains:

```text
[propext, Classical.choice, Quot.sound]
```

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Scope the code-separation theorem:

```text
CODEX-F3-TERMINAL-NEIGHBOR-CODE-SEPARATION-SCOPE-001
```
