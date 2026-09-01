# CMP89 Eq. (2.46): fine-to-fine Fourier/operator dictionary

Status: the holomorphy predecessor is cold-sealed; the neutral transposed
arbitrary-source solution is promoted PRE-VALIDATION and remains outside the
import graph pending its own compiler and axiom gates.

## Exact endpoint

Construct the finite periodic fine-to-fine Green column directly from the
literal point-source solution of (2.46), prove that the already sealed
full-box precision sends it to the named finite point source, and identify it
with the internally generated full-box Green by inverse uniqueness.

The proof must construct the identity internally.  It may not accept an
equality between the alias solution and a physical inverse, a right inverse,
or a regional Green as input.

The continuous object
`cmp89Eq246NormalizedPhysicalFineToFineGreen` is deliberately *not* the
starting point of this finite identification.  Equating its periodization
with the periodic Green is a later Poisson/periodization theorem and needs
absolute summability.  Requiring that theorem here would make the route to
the exponential bound circular.

## Finite chain

1. **Pin the periodic scales.**  Use
   `M = L^j`, a named coarse side `N'`, and full fine side `M*N'`.  Keep the
   scalar mass and the averaging coefficient separate.  The finite action is
   the already sealed `cmp99SourceFlatFullComplexPrecisionAction`; no new
   precision is selected.

2. **Reuse the exact alias/fibre equivalence.**  Reindex the literal
   `CMP89Eq246AliasIndex 4 L j` through
   `cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv` (or its exact
   neutral predecessor) at one coarse momentum.  Prove the alias momentum,
   diagonal symbol, averaging column, and opposite-momentum row identities
   separately.  Orientation is fixed by the existing transposed DFT column
   theorem, not by abstract self-adjointness.

3. **Discrete point-source solution.**  At each coarse reciprocal mode,
   instantiate `cmp89Eq246StabilizedFinePointSourceSolution` with the Fourier
   phase of one named fine source.  Synthesize those coefficients by the
   sealed finite DFT.  This defines a finite periodic full-G column; it does
   not insert `Q_j^*` and must not reuse the existing (2.48) particular
   solution, which is the `G Q_j^*` lane.

4. **Finite delta reconstruction.**  Use
   `cmp99FlatComplexFibrePointSource_eq_normalized_sum_fourierMode` and the
   exact source character to reconstruct the literal finite point source.
   All volume factors remain visible.  No continuous Brillouin Jacobian is
   involved in this finite statement.

5. **Physical fibre equation.**  Transport the sealed (2.46) matrix equation
   through the alias/fibre dictionary and the already sealed theorem
   `cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fourierMode`.
   Sum over coarse modes.  The conclusion is the literal full-box precision
   applied to the internally synthesized column equals the literal point
   source.

6. **Identify by uniqueness.**  Apply the existing ordered inverse law of
   the internally generated full-box Green to the right-inverse equation.
   This produces the equality with the generated physical Green column; the
   equality is a theorem, never an input record field.

7. **Continuous/discrete bridge, later.**  Only after an exponential bound
   for the full Eq. (2.46) kernel is available, prove that periodizing
   `cmp89Eq246NormalizedPhysicalFineToFineGreen` over translations by the
   full fine side gives the finite Green just identified.  Reuse the sealed
   finite-grid aliasing/torus machinery where applicable.  The fine-scale
   phase no-go forbids dropping `xi` from an alias phase.

8. **Stop before the regional claim.**  The half-open Neumann rectangle,
   method-of-images identity (2.42), regional compression, uniform
   `B0`/`delta0`, window 15, terminal fields, `20/41`, and `TermSource` are
   downstream and remain open.

## Acceptance gates

- The periodic synthesis carries the exact centered even/odd alias convention
  already sealed in `CMP89Eq246AliasIndex` and the exact fixed-fibre
  equivalence already present in the tree.
- The proof cites the fine-phase scale no-go and never drops `xi` from an
  alias phase.
- The spatial precision is the existing literal full-box physical precision,
  and its equality with the (2.46) fibre matrix is proved componentwise.
- The full `G_j` is not identified with the typed (2.48) `G_j Q_j^*` lane.
- No absolute-summability or periodization hypothesis is smuggled into the
  finite inverse proof; those belong to the later continuous/discrete bridge.
- The final audit names every new source-facing definition/theorem and uses
  only `{propext, Classical.choice, Quot.sound}` or a strict subset.
- This brick does not move `20/41` and does not instantiate `TermSource`.

## Sealed inputs already present

- `cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv`: fixed-fibre to
  centered signed alias index.
- `cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fourierMode`:
  literal full-box precision as the transposed physical alias matrix on one
  mode.
- `cmp99FlatComplexFibrePointSource_eq_normalized_sum_fourierMode`: exact
  finite delta reconstruction with product-volume normalization.
- `cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM_comp_precision`: ordered
  inverse law needed for uniqueness.
- The existing `SourceSeparated...GreenQprimeStar...` chain is precedent for
  DFT normalization and endpoint orientation only.  It consumes a coarse
  point source through `Q'^*` and therefore cannot be reused as the full-G
  theorem.

## First promoted brick after the current cold seal

The entrywise physical-to-CMP89 matrix dictionary and its two-axis
reindexing are already sealed as
`cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_entry_eq_cmp89` and
`cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_reindexed_eq_cmp89`.
They must be reused, not reproved.

The remaining orientation mismatch is real: the physical DFT action is the
**transpose** of that matrix, while the current arbitrary-source construction
`cmp89Eq246StabilizedAliasFullSolution` solves the non-transposed system.
The existing Eq. (2.47) transpose solution handles only the special averaging
row source and therefore is not the full point-source solution.

The first promoted brick is consequently neutral finite algebra:

1. construct the central-stabilized solution of the **transposed** Eq. (2.46)
   alias matrix for an arbitrary source by swapping the printed column/row
   roles in the already sealed full-solution algebra;
2. prove `K.transpose.mulVec solution = source` with the same noncentral,
   stabilized-denominator and central-column nonvanishing gates;
3. only in the following physical brick, pull that solution and the exact
   fine point-source phase through the fixed-fibre equivalence.

The neutral transpose brick contains no `FinBox`, coarse-mode sum, Green CLM,
periodization or analytic bound.  It is the smallest unit that can falsify
the actual orientation obstruction before physical synthesis is built above
it.  Abstract self-adjointness or equality of block norms is not an accepted
repair.

### Exact neutral algebra to promote

Write `c` for the central alias, `f` for the fine diagonal, `u` for the
printed column and `v` for the printed opposite-momentum row.  Since

```text
K = diag(f) + a u v^T,
K^T = diag(f) + a v u^T,
```

the transposed arbitrary-source construction must use the **column** moment
and the column central gate (not the row versions used by the existing full
solution):

```text
baseT(source)   = sum_{n != c} u_n source_n / f_n
momentT(source) = (u_c source_c + f_c baseT(source)) / stabilized

solutionT_n = source_n / f_n - a v_n momentT(source) / f_n,  n != c
solutionT_c = (momentT(source)
               - sum_{n != c} u_n solutionT_n) / u_c.
```

The public theorem is literally

```text
K.transpose.mulVec solutionT = source
```

under exactly three gates: noncentral `f_n != 0`, the named stabilized
denominator nonzero, and `u_c != 0`.  The last gate is distinct from the
`v_c != 0` gate of `cmp89Eq246StabilizedAliasFullSolution`; silently reusing
the latter would solve the wrong orientation.  The proof must first expose
`sum u_n * solutionT_n = momentT` and then split the matrix equation into the
central and noncentral branches.  No new denominator or source hypothesis is
permitted.

The later strip consumer discharges `u_c != 0` from the already sealed
nonvanishing of `u_c v_c`; it does not introduce a sixteenth window.  The
existing row lemma proves the `v_c` projection, so the transpose brick must
add the symmetric column projection explicitly rather than reuse the row
statement by name.
