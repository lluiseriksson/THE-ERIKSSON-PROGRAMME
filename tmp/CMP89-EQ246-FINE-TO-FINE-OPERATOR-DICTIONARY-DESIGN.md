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

## Post-synthesis analytic chain (2026-09-01)

The neutral transpose algebra, physical pullback, finite point-source DFT,
full periodic point-source solution and inverse-uniqueness endpoint have now
all been constructed.  Their final generated-Green gate is running as the
single cold Colab v3 seal at source checkpoint
`d9a14b9c8705dd709712e7baba68b82e3b15435a`; until its terminal evidence is
verified these last three endpoint files remain PRE-VALIDATION.

Even a green v3 endpoint does **not** prove the continuous fine-to-fine
kernel or CMP89 (2.42).  The remaining bridge is the following finite chain:

1. **Physical point-source phase bound.**  On the full common polistrip,
   bound every component of
   `cmp89Eq246FinePointSourceAliasVector` at the physical source endpoint.
   The reciprocal alias shifts are real, so the modulus depends only on the
   common imaginary part and the source coordinate.  No false claim that
   individual aliases have identical phase is allowed: the shift is `2*pi*m`
   while the fine endpoint is scaled by `(L^j)^-1`.
2. **Moment bound.**  Bound
   `cmp89Eq246StabilizedAliasFullSolutionMoment` from the sealed
   noncentral-fine-symbol estimates, central averaging factors and the named
   stabilized reciprocal.  The finite alias cardinality may not appear as
   `(L^j)^4`; it must be absorbed by the existing radial/source-weight sums.
3. **Full solution bound.**  Bound both the central and noncentral branches
   of `cmp89Eq246StabilizedFinePointSourceSolution`, then sum the target
   synthesis over aliases.  The central row lower bound and the
   stabilized-denominator window stay distinct and visible.
4. **Relative endpoint decay.**  Multiply the target phase by the source
   bound and shift each complex coordinate with the sign of
   `target-source`.  Because all alias shifts are real, the exponential
   modulus is the single physical factor
   `exp (-rho * xi * ||target-source||_1)`.  This is a joint endpoint
   argument, not two incompatible contour shifts.

   This item is a finite four-brick chain.  The existing absolute source
   estimate `exp (rho * ||source||_1)` is intentionally not an input to its
   last step, because taking that norm first destroys translation-invariant
   decay.

   1. Prove the exact algebraic product of the target synthesis phase and
      the literal fine-point-source phase.  On the signed contour selected
      by `targetEndpoint - sourceEndpoint`, its norm is exactly the relative
      `ell^1` exponential.  Because the rank-one branch mixes alias indices,
      also expose the target decay and source growth as two alias-independent
      directed scalar factors and prove their exact recombination.  A
      same-alias phase identity alone is not a producer for that branch.
   2. State the source estimates with an arbitrary nonnegative common
      envelope `g`, supplied pointwise for every alias.  Transport that same
      `g` through the noncentral source moment and stabilized solution
      moment; do not replace it by an absolute endpoint norm.
   3. Transport the common envelope through the bare diagonal, rank-one and
      central branches.  The bare branch must retain the literal
      `256 * (L^j + 1)^2` loss, while the other two branches remain
      scale-uniform.
   4. Specialize `g` to the directed source phase on the signed contour and
      combine it with the target phase before the final norm.  The theorem
      delivered to the contour telescope must display
      `targetEndpoint - sourceEndpoint` literally.
5. **Continuous Green certificate.**  Iterate the one-coordinate contour
   theorem over all four coordinates, retain the literal normalized
   Brillouin factor, and obtain an explicit `B0` and fine rate
   `delta0 = rho / L^j` for
   `cmp89Eq246NormalizedPhysicalFineToFineGreen`.
6. **Summability and finite-grid periodization.**  Use the resulting l1
   exponential bound to prove absolute summability, then apply the sealed
   generic finite-grid aliasing theorem.  Only here may the periodization of
   the continuous kernel be identified with the finite periodic point-source
   Green certified by the v3 endpoint.
7. **Neumann continuation.**  Feed that fine-to-fine kernel into the
   Laplacian, retained-`Q'`, mass and operator/sum reflection chain.  The
   typed CMP89 (2.48) `G_j Q_j^*` object remains a separate downstream
   composition and is never substituted for this kernel.

### Orientation gate before periodization (2026-09-02)

The continuous full-point-source object currently used by the contour lane
is built from `cmp89Eq246StabilizedAliasFullSolution`; its defining fibre
equation is

```text
K.mulVec solution = source.
```

The finite physical point-source construction is deliberately built from
`cmp89Eq246StabilizedAliasTransposeFullSolution`, because the sealed physical
DFT action is the transpose of the printed alias matrix:

```text
K.transpose.mulVec solutionT = source.
```

Consequently the continuous/discrete bridge in item 6 must not identify the
two solutions by notation, abstract self-adjointness, or equality of block
norms.  Before finite-grid periodization is allowed to consume the continuous
kernel, the tree must construct one of the following equivalent source-facing
facts:

1. a cross-fibre Fourier-negation theorem carrying the complete transposed
   point-source solution to the complete non-transposed solution, with the
   target/source swap and every endpoint phase written literally; or
2. an equality between the periodized continuous kernel with the explicitly
   swapped endpoint orientation and the finite physical point-source
   solution.

The already sealed `cmp99SourceCenteredAliasVectorReflection` and
`cmp99SourceFlatQprimeFixedCoarseFibreFourierNegEquiv` provide the carrier
permutations, while the existing cross-fibre quotient bridge is precedent
only for the special Eq. (2.47) row/column solution.  It is not a proof for
the arbitrary-source full solution.  The new gate must cover the central
branch as well as every noncentral alias and must derive the source phase
transport from the literal fine endpoint.

Until this gate is proved, the exponential bound for
`cmp89Eq246NormalizedPhysicalFineToFineGreen` is a valid continuous-kernel
estimate but is not yet a bound for the generated finite periodic Green.

### Acceptance gate after the source-moment brick

The scale-uniform source moment controls only the rank-one correction.  It
does not make the bare diagonal branch

```text
source_m / fine_m
```

summable with the reciprocal-alias weight used for the averaging quotients.
In four dimensions its absolute alias sum has the physical inverse-Laplacian
scale `O((L^j)^2)`, rather than a scale-independent constant.  The next
solution theorem must therefore split the two species explicitly:

1. the diagonal branch carries the visible value scale `(L^j)^2` (or an
   equivalent normalized Brillouin integral bound);
2. the rank-one branch consumes the scale-uniform moment and the already
   summable averaging-column quotient;
3. the central branch consumes a named quantitative reciprocal bound for the
   central row, derived from the central-pair floor and the column upper
   bound, not merely its nonvanishing.

No theorem may claim a scale-uniform absolute alias sum for the bare diagonal
branch.  Such a claim would erase the first entry of the printed CMP99 (3.42)
scale vector `[ell^2, ell, ell, 1]`.

Likewise, the absolute strip estimate
`exp(rho * ||sourceEndpoint||_1)` is only a uniform holomorphic majorant.  It
cannot by itself be multiplied by the target phase to infer translation-
invariant decay.  The relative endpoint phase must be combined algebraically
before taking norms (or the kernel must first be reduced by a proved
translation-covariance theorem).  The later contour theorem must expose
`targetEndpoint - sourceEndpoint` literally.

The old PRE-VALIDATION module
`BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalInverseProducer`
uses the withdrawn same-scale (2.48) wrapper and is retained only as
conditional algebra.  It is not a target of the next compiler queue.
