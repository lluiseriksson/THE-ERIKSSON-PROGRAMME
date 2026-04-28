# F3 Residual-Only Selector Counterexample Search

Timestamp: 2026-04-26T18:55:00Z

Task: `CODEX-F3-RESIDUAL-SELECTOR-COUNTEREXAMPLE-SEARCH-001`

## Scope

This is a bounded finite-model search, not a Lean theorem and not a proof of any
universal statement.  The model is aligned with the project definition of
`plaquetteGraph`:

```lean
Adj p q := p ≠ q ∧ siteLatticeDist p.site q.site ≤ 1
```

The script represents a concrete plaquette as `(site, dir1, dir2)` with
`dir1 < dir2`; adjacency ignores orientation except for vertex equality, exactly
as the current `plaquetteGraph` does.

Script:

```text
scripts/f3_residual_selector_counterexample_search.py
```

## CSP Tested

For fixed `(d, L, root, k)`, the search forms all anchored connected buckets
`X` of size `k`.  A residual-only selector is encoded as a CSP:

- variable: each residual `R = X.erase z`;
- domain: `parent(R) ∈ R`;
- clause for each current bucket `X`: at least one safe deletion `z` must have
  `parent(X.erase z)` adjacent to `z`.

This is the finite analogue of the v2.71/v2.72 obligation:

```lean
PhysicalPlaquetteGraphResidualExtensionCompatibility1296
```

It deliberately does not allow the parent to be chosen post-hoc from the
current `(X,z)` witness.

## Reproducible Output

Command:

```powershell
python scripts\f3_residual_selector_counterexample_search.py
```

Output:

```text
{'d': 2, 'L': 2, 'k': 2, 'root': ((0, 0), (0, 1)), 'vertices': 4, 'anchored_connected_buckets': 2, 'residual_variables': 1, 'clauses': 2, 'ambiguous_residuals': 1, 'satisfiable': True, 'sample_assignment_size': 1}
{'d': 2, 'L': 2, 'k': 3, 'root': ((0, 0), (0, 1)), 'vertices': 4, 'anchored_connected_buckets': 3, 'residual_variables': 2, 'clauses': 3, 'ambiguous_residuals': 2, 'satisfiable': False, 'sample_assignment_size': 0}
{'d': 2, 'L': 3, 'k': 3, 'root': ((0, 0), (0, 1)), 'vertices': 9, 'anchored_connected_buckets': 5, 'residual_variables': 2, 'clauses': 5, 'ambiguous_residuals': 2, 'satisfiable': False, 'sample_assignment_size': 0}
{'d': 3, 'L': 2, 'k': 3, 'root': ((0, 0, 0), (0, 1)), 'vertices': 24, 'anchored_connected_buckets': 109, 'residual_variables': 11, 'clauses': 109, 'ambiguous_residuals': 11, 'satisfiable': False, 'sample_assignment_size': 0}
{'d': 4, 'L': 1, 'k': 3, 'root': ((0, 0, 0, 0), (0, 1)), 'vertices': 6, 'anchored_connected_buckets': 10, 'residual_variables': 5, 'clauses': 10, 'ambiguous_residuals': 5, 'satisfiable': True, 'sample_assignment_size': 5}
{'d': 4, 'L': 2, 'k': 3, 'root': ((0, 0, 0, 0), (0, 1)), 'vertices': 96, 'anchored_connected_buckets': 838, 'residual_variables': 29, 'clauses': 838, 'ambiguous_residuals': 29, 'satisfiable': False, 'sample_assignment_size': 0}
```

## Counterexample Pattern

The obstruction already appears in the physical dimension at `(d = 4, L = 2,
k = 3)`.  It is the same square-corner pattern visible in the small `d = 2`
submodel.

Use a fixed orientation `(0,1)` and four sites:

```text
r = (0,0,0,0)
a = (1,0,0,0)
b = (0,1,0,0)
c = (1,1,0,0)
```

Distances:

- `r` is adjacent to `a` and `b`;
- `a` is adjacent to `c`;
- `b` is adjacent to `c`;
- `r` is not adjacent to `c`;
- `a` is not adjacent to `b`.

The three anchored size-3 buckets are connected:

```text
X0 = {r, a, b}
X1 = {r, a, c}
X2 = {r, b, c}
```

For `X1`, the only safe deletion is `c`, leaving residual `{r,a}`; since `c`
is adjacent to `a` but not to `r`, compatibility forces
`parent({r,a}) = a`.

For `X2`, the only safe deletion is `c`, leaving residual `{r,b}`; since `c`
is adjacent to `b` but not to `r`, compatibility forces
`parent({r,b}) = b`.

For `X0`, the safe deletions are `a` and `b`.  Deleting `b` leaves `{r,a}` and
requires `parent({r,a}) = r`; deleting `a` leaves `{r,b}` and requires
`parent({r,b}) = r`.  Both conflict with the forced assignments above.

So the current residual-only parent selector shape is not compatible with this
finite physical plaquette-graph pattern.

## Consequence

This supports the v2.72 diagnosis: the present residual-only selector target is
too strong for the current decoder symbol.  The next honest design move is not
to keep trying to prove:

```lean
PhysicalPlaquetteGraphResidualExtensionCompatibility1296
```

as currently stated.  Instead, scope a symbol/deletion-rule strengthening that
records enough extension information to break the square-corner ambiguity.

Minimal candidates for the next task:

1. Add a residual-extension branch symbol that distinguishes which residual
   frontier edge is being used.
2. Restrict the deletion rule to a deterministic deletion order whose residual
   parent is chosen together with the residual.
3. Strengthen the decoder symbol beyond `residual + Fin 1296` so it includes a
   parent-selection witness or branch index.

## Project Status

No Lean theorem was added.  No `UNCONDITIONALITY_LEDGER.md` row was upgraded.
`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No Clay, lattice, honest-discount,
named-frontier, README, or planner percentage moved.
