# CMP99 Section-C parser audit

## Scope

This audit isolates the source-to-Lean boundary behind CMP99 pages 411--416.
It does not add a producer and does not move the `18/41` terminal counter.
The source object is the linear generalized-walk expansion of the square
propagator `G` in (3.107), followed by the rectangular composition (3.126),
the source coordinate convention after (3.133), and Theorem 3.12.  Equation
(3.107) alone is not an expansion of the physical minimizer `H`.

## What the tree already proves exactly

| Layer | Exact repository object | Status |
|---|---|---|
| three displayed summands of (3.95) | `BalabanCMP99Eq395Algebra` | exact noncommutative identity |
| finite signed correction alphabet | `CMP99Eq395CorrectionSpecies` and `cmp99Eq395RAtom` | exhaustive at the top level |
| Neumann powers of that correction | `cmp99Eq395R_pow_eq_sum_ordered_atoms` | every ordered top-level word |
| corrected physical covariance | `cmp99Eq395PhysicalCorrectedCovariance_eq_tsum_ordered_atom_layers` | exact top-level reconstruction |
| dependent factor words | `DependentArrowWalk` | carrier endpoints retained definitionally |
| Section-C grouping grammar | `CMP99SectionCGroupedFactor` | exact flatten/evaluate preservation and at most three attachments |
| weakening carrier under grouping | `CMP99SectionCGroupedWalk.flatten_active` | fresh-clone verified at `1d986237...` |
| target-total endpoint | `CMP116Lemma1DependentTargetWalkSourceCertificate` | fresh-clone verified at `fe5bfdd2...` |

The three (3.95) species are composite operators, not Section-C atom roles:

```text
first  = (1 - chi) A (h C h)
second = chi (A - A_D) (h C h)
third  = (chi A_D h - h chi A_D) C h.
```

Consequently, the exact ordered words in
`BalabanCMP99SourceEq395WalkExpansion` are words of composite correction
summands.  Labelling those three species directly as `smallAnchor`,
`attachToRightAnchor`, `attachToLeftAnchor`, or `sealedAnchor` would change the
source factorization.

## The missing parser stage

For each source cell and each of the three correction species, the physical
producer must perform these operations in order:

1. expand every internal `G` or `G'` occurrence into its complete dependent
   generalized-walk family;
2. expose one dependent factor word for every resulting summand, retaining
   all intermediate and terminal carriers;
3. prove that the summable evaluation of those words is exactly the original
   composite (3.95) atom;
4. classify the exposed factors as the small `K(h') G h'` anchors or the
   nonsmall `h' G' h'` / `h C h` attachments printed on pages 411--413;
5. apply the closest-anchor rules and prove the printed bound of at most three
   attached nonsmall factors;
6. transport the grouped dependent words through the rectangular readout and
   prove the one target-total reconstruction required by
   `CMP116Lemma1DependentTargetWalkSourceCertificate`.

The parser output must therefore carry both an exact evaluation theorem and a
role/grouping theorem.  A list of guessed `alpha` labels, a free family of
weakened operators, or one reconstruction hypothesis per independently chosen
target is not an admissible substitute.

### Literal alphabet constraints from (3.98) and (3.107)

Printed page 413 / PDF page 25 and printed page 416 / PDF page 28 were checked
visually against the primary PDF.  They impose more than an untyped list of
localized factors:

- `alpha` enumerates the finitely many factor shapes attached to one
  localization domain `X`;
- `0` is a distinguished label with
  `R'_0(square) = h_square C_square h_square` and `R'_0(X) = 0` when `X` is
  larger than one partition square;
- every displayed walk starts with `(alpha_0, X_0) = (0, X_0)`;
- consecutive localization domains satisfy `X_(i-1) intersect X_i != empty`;
  and
- the source warns that factors may act between different scales, so only
  carrier-compatible label sequences are admissible even though this typing is
  suppressed in the displayed sums.

`DependentArrowWalk` records the last item, and `CMP99SectionCGroupedFactor`
records the source grouping roles and the at-most-three attachment bound.  The
current `CMP116Lemma1DependentWalkSourceCertificate`, however, accepts an
arbitrary typed walk index and does not by itself force the distinguished
initial label or the source normalization of `R'_0`.  Those are obligations of
the missing physical parser.  They must be proved before its single
`fullCoupling_reconstruction` field can be cited as the literal (3.107)
reconstruction rather than as a generic walk sum.

## Reuse boundary

`cmp116Lemma1PhysicalCovariancePropagator_eq` is an exact squarefree bridge for
the specialized Pi4 covariance `G(s)`.  It is useful substrate for step 1, but
it does not identify that Pi4 object with every regional `C_D` or `G'` inside
the (3.95) species.  The missing regional/source-carrier dictionary must be
proved before this bridge can discharge an internal factor.

Likewise, `BalabanCMP116Lemma1PhysicalMinimizerPropagator` is not reusable for
the printed `H(s)`: it expands the algebraic inverse with multiplicities and
agrees with the physical minimizer only at full coupling.  Its own module
records this source-dictionary retraction.

### Why projected-inverse uniqueness does not yet supply the dictionary

There are two exact inverse packages in the tree, but they are not inverses of
the same operator on the same carrier:

- `cmp116Lemma1PhysicalCovariancePropagator_eq` reconstructs the Pi4
  covariance `G(s)` on fine physical one-cochains.  Applying the literal block
  map produces `cmp99SourcePi4WeakenedCoarseMiddle = Q G(s) Q*` on coarse
  physical one-cochains; at `s = 1` this is identified with the physical
  middle of (3.126).
- `generatedPhysicalCoarseCovarianceMiddleCoordinates_comp_covariance`
  concerns the regional generated middle `Q' (G')^2 Q'^*` and its inverse on
  active gauge zero-cochains.  Its ambient version gives the regional
  characteristic projector, not the identity on the whole torus.

The first construction depends on a fine physical endomorphism `K`; the
second is generated from the regional covariant Laplacian, mass term, iterated
`Q'` tower, and active region.  No theorem in the inspected tree identifies
`Q G(1) Q*` with `Q' (G')^2 Q'^*`, identifies their carriers, or makes the Pi4
walk covariance a right inverse of the regional middle.  Therefore
right-inverse uniqueness cannot prove the missing regional walk dictionary
from the present endpoints.  Assuming that common-middle identification would
only relocate the CMP99 reconstruction hypothesis.

## Next source-facing unit

The next unit is below any one-species expansion.  CMP99 Theorem 3.7 and
equations (3.87)--(3.90), visually checked on printed pages 408--410 / PDF
pages 20--22 of the primary PDF with SHA-256
`39F8033B35838C7BDD14F97C7FB1EDB0B35D4190B8B88F31D19D12A72D542861`, give
the exact regional construction:

```text
G'_0 = sum_Pi h_Pi G'_Pi h_Pi,
Delta' G'_0 = I - sum_Pi K(h_Pi) G'_Pi h_Pi = I - R',
G' = G'_0 (I - R')^-1 = G'_0 sum_n (R')^n.
```

Thus the missing producer is specifically the physical specialization of
this regional Neumann expansion on one common active fine zero-cochain carrier;
it is not equation (3.107), which later expands the different square
propagator `G`.  Its statement must fix internally:

- one ambient regional precision and active carrier;
- the finite square partition and the linear walk alphabet of square sequences
  with consecutive intersections;
- every local Dirichlet Green, extended by zero to that common carrier;
- the partition multipliers, commutator factors, defect contraction and
  Neumann summation; and
- the equality of the walk sum with that literal regional `G'`.

It must not receive an already chosen walk sum or a free equality to `G'`.
Only after this regional Green dictionary exists is a one-species expansion
implementable: substitute the exact `G'` expansion into a literal (3.95)
species, prove evaluation back to that species, and then apply the existing
grouping grammar.  The Pi4 `G(s)` bridge remains useful for the separate
global one-cochain factor, but is not a replacement for this regional
zero-cochain reconstruction.

There are two distinct support requirements in this step.  For the exact
operator identity it is enough that the multiplier `h_Pi` be supported in its
Dirichlet region: the local Green is generated from the literal compression
`R Delta' E`, and the outer multiplier permits insertion of `E R` after
`Delta'`.  No finite-range premise is used in that algebra.  The later
analytic estimate is stronger.  To prove sparsity of consecutive correction
factors and make the regional defect contractive, the physical specialization
must expose a collar condition of the form

```text
finiteRange < dist(supp h_Pi, complement Omega_Pi).
```

That collar is not implied by mere support inclusion and may not be hidden in
the partition dictionary.  Likewise, the regional condition `norm R' < 1` is
not the existing `patchedDefect_small` field: the latter controls
`cmp99PatchedPhysicalParametrixDefect` on physical one-cochains, whereas `R'`
acts on the regional zero-cochain carrier.  It is therefore a separate scalar
target in the joint smallness registry, with its physical attainment left to
the finite-range/commutator estimates.

The dependent-arrow alphabet and changing intermediate carriers recorded on
printed page 413 belong to the later cross-scale Section-C expansion.  They
must not be imported into (3.90), whose displayed walks are ordinary linear
sequences of partition squares acting on a common carrier.

### Immediate source-to-tree dictionary

The repository already has the faithful base layer for Theorem 3.7:

- `cmp99OmegaDirichletZeroPrecision` compresses one ambient precision to a
  regional zero-boundary problem;
- `cmp99OmegaDirichletZeroGreen` is its two-sided inverse; and
- `cmp99OmegaSourceGaugeDirichletGreen` specializes the same construction to
  an ambient source-gauge precision with an explicit `Qprime`.

This is the correct layer on which to formalize the algebra of (3.87)--(3.90).
The still-open physical dictionary is the identification of the source's one
ambient `Delta'_a` and `Q'` with the generated physical precision/Green tower
used by the Section-C factors.  It is **not** licensed to identify each
region-specific generated precision with a compression of a larger generated
precision: the existing `cmp99TypedPrecisionDefect` records a genuine
transition mismatch between such generated levels.  Any specialization must
therefore prove the ambient/generated identification explicitly rather than
receive the final equality of Green operators as a free input.

### What the existing Eq. (3.95) Neumann chain does not replace

The repository already proves a complete but different inverse construction:

- `cmp99Eq395PhysicalPatchedCovariance` is the coarse regional sum
  `sum_Pi h_Pi C_Pi h_Pi`;
- `cmp99Eq395PhysicalCorrection` is the exhaustive three-species correction
  in (3.95);
- `cmp99Eq395PhysicalCorrectedCovariance_eq_tsum_ordered_atom_layers` expands
  all powers of that correction; and
- `cmp99Eq395PhysicalCorrectedCovariance_eq_canonical` identifies the
  convergent sum with the canonical inverse of the global middle
  `Q' (G')^2 Q'^*`.

This is a reconstruction of the **coarse covariance**
`(Q' (G')^2 Q'^*)^-1`, not of the fine regional Green operator
`G' = (Delta')^-1`.  Its local covariance factors still contain the literal
generated `G'` internally.  Therefore neither the exact (3.95) correction
alphabet nor right-inverse uniqueness can discharge the (3.90) dictionary.
Using either as though it were the regional `G'` series would conflate both
the operator and its carrier.
