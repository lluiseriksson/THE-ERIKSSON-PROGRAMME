# CMP89 Neumann next gates — static checkpoint

Status: design-only checkpoint.  The boundary no-go is cold-sealed at
`1721fb8b8655e4e6f9bb15fc0e0440750ff013d9`, with durable evidence recorded
by sealing commit `6d48122b`.  The first three-term precision hot diagnostic
failed only at the two local-let rewrites in the coercivity proof; the exact
error is preserved and the two normalizations are repaired for a retained
runtime retry.  Neither a hot PASS nor this checkpoint is seal authority.  No
counter moves.

## What is fixed

- The regional derivative is the internal-bond Neumann operator
  `cmp89SourceNeumannRegionalCovariantD0CLM`.
- The regional precision is the literal three-term sum
  `D_N^* D_N + mass^2 id + a_count Q'_r^* Q'_r`.
- The retained specialization fixes `Q'_r` from one
  `CMP99SourceRetainedPhysicalTower` and fixes `a_count` through
  `cmp85SourcePrefixCountingCoefficient`; no arbitrary average or second
  volume conversion remains.
- The existing zero-extension Dirichlet derivative is not definitionally or
  extensionally equal to the Neumann derivative at a boundary-crossing bond.
  That negative is now compiler-verified; it is no longer merely a design
  warning.

The word "literal" above refers to the three-term operator order on the
counting-Hilbert presentation.  Source equality still has a separate measure
dictionary: CMP89 (1.3) places the same `eta^d` factor in the site and bond
quadratic forms, while the current `PiLp` operator is unweighted.  The common
factor should cancel in the induced Laplacian, but that cancellation is not
yet a theorem and must not be inferred from matching dimensions.

## Exact remaining analytic gate for the canonical inverse

The first reduction is the literal joint-kernel statement

```text
D_N phi = 0  and  Q'_r phi = 0  implies  phi = 0.
```

Finite-dimensional anti-Lipschitz compactness then constructs some positive
`CP` and hence the named `CMP89SourceRetainedNeumannPrefixPoincare` predicate.
The promoted PRE-VALIDATION module
`BalabanCMP89SourceNeumannRegionalPoincareExistence.lean` records this
reduction, with `Qprime` fixed to `(T.towerAt r).Qprime` in its retained
specialization.  It does not provide a uniform or explicit `CP`; therefore it
is not by itself the quantitative CMP89 producer.

The source-facing proof of the joint-kernel gate should use the block-saturated
retained region and the same physical `Q'_r`.  A Dirichlet Poincare theorem
cannot simply be rewritten: the zero-extension energy contains boundary
bonds absent from `D_N`.

The sealed identity
`Q'_r.comp weightedAdjoint_r = normalization_r • id` does not discharge this
gate by itself.  It proves the retained average is split-surjective (for
positive normalization), not injective; a vector may lie in `ker Q'_r`.
Therefore the missing content is precisely that the internal-bond
covariantly-constant subspace meets this kernel only at zero.  Any future
proof must use the geometry/background transport of that subspace, rather
than citing tower normalization alone.

The existing source-generated regional Poincare chain is also not this
producer.  Its one-scale theorem is explicitly Dirichlet: it applies the full
periodic estimate to `extendZeroZeroCLM` and therefore includes
boundary-crossing covariant differences.  The cold-sealed boundary no-go
shows that this energy cannot be rewritten as the internal-bond Neumann
energy.  Any Neumann proof must instead use the exact internal connectivity
and the literal transported-average recursion.

## Independent representation gate

The current `CMP89NeumannReflectionRepresentationCertificate` only states
summability and equality of a supplied scalar regional kernel with the image
series.  It does not tie that kernel to the inverse of the literal three-term
precision.  A physical bridge must additionally prove one of:

1. the image-series operator is a two-sided inverse of the literal Neumann
   precision, followed by inverse uniqueness; or
2. equality of the image-series kernel with the already constructed canonical
   inverse, using an explicit evaluation/kernel dictionary.

Instantiating the representation certificate with the series by definition is
not accepted: that would prove the printed series shape without proving it is
the Green of the physical operator.

There is also a fibre gate that cannot be suppressed by notation.  The
canonical inverse constructed above acts on
`ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)`, whereas the currently sealed
physical image-series consumer specializes its kernel values to `ℂ`.  A valid
dictionary must therefore expose one of the following before inverse
uniqueness is applicable:

- an operator-valued version of the reflection certificate, with each kernel
  value acting on `SUNLieCoord Nc`; or
- a proved fibre diagonalization/intertwiner showing that the literal gauge
  precision reduces to the scalar kernel used by the existing CMP89 (2.48)
  route.

No scalar kernel may be identified with the gauge-valued canonical inverse by
definition.  This fibre dictionary is logically independent of convergence of
the reflection series.

The design-only pair
`BalabanCMP89CanonicalNeumannReflectionRepresentation.draft.lean` and its
audit now removes the free regional kernel at the type boundary.  Its retained
specialization defines every regional entry by applying
`cmp89SourceRetainedNeumannPrefixGreen` to a single-site fibre probe and then
evaluating at the target.  The half-open rectangle equivalence and the
operator-valued full-lattice action remain visible inputs.  This is only a
signature check until the literal precision and Poincare bricks compile; it
does not yet prove the reflection equality or create the full-lattice action.

This does **not** reopen the coordinate complexification from scratch.
`BalabanCMP99PhysicalFibreComplexification` and the later flat physical-fibre
Fourier bricks already seal the injective coordinatewise complexification and
vector-valued flat stencil diagonalization.  The remaining work is the
regional/operator transport for the literal Neumann precision (including its
`Qprime` term) and inverse uniqueness.  Those sealed flat lemmas are inputs to
the gate, not substitutes for it.

## Finite route to the uniform localized value action

1. validate the literal three-term counting-Hilbert precision and its
   canonical inverse;
2. prove the common-`eta^d` source/counting measure cancellation;
3. discharge the retained Neumann joint-kernel/Poincare gate, or construct the
   image-series inverse directly;
4. identify the half-open source rectangle and the evaluation kernel of that
   same inverse;
5. construct operator-valued CMP89 (2.42) for the full fibre;
6. transport the already sealed flat physical-fibre complexification and
   Fourier diagonalization through the literal `Qprime` term, regional
   restriction and inverse-uniqueness gate;
7. consume the cold-sealed owner-kernel bound;
8. feed the resulting arbitrary-field localized value action to the
   cold-sealed CMP99 (3.42) value-to-four-actions adapter.

No step above attains window 15 until the downstream (3.89) contraction is
proved.  Live counters remain exactly `20/41`, `TermSource = 0`.
