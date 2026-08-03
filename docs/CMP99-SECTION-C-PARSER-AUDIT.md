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

## Next implementable unit

The next Lean unit should not be the whole parser.  It should expose one
source-faithful internal expansion for one literal (3.95) species, with:

- a dependent word index;
- exact evaluation back to that species;
- the squarefree union of visited cubes; and
- no grouping-role claim until the printed factor types are present.

Only after that first species is exact should the construction be generalized
to all three and connected to `CMP99SectionCGroupedFactor`.
