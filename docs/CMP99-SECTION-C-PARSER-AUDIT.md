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

The internal formula for `K(h)` is also visually fixed now.  Printed page
409 / PDF page 21 of the same primary artifact expands
`Delta'_a (h lambda)` into exactly three correction species before identifying
their sum with `K(h) lambda`:

```text
Delta'_a(h lambda)(x)
  = h(x) Delta'_a(lambda)(x)
    - sum_{b in st(x)} (partial h)(b) (D lambda)(b)
    + (Delta h)(x) lambda(x)
    + a_j (L^j eta)^(-2) sum_{x' in B_j(y)} L^(-jd)
        (partial h)(Gamma_xy^(j) union Gamma_yx'^(j))
        R(U(Gamma_yx^(j))^(-1)) R(U(Gamma_yx'^(j))) lambda(x')
  = h(x) Delta'_a(lambda)(x) - (K(h) lambda)(x).
```

This is a literal formula gate, not merely a bound.  In particular, the
`Q'^* a Q'` species retains the normalized `L^(-jd)` row mass printed in the
source; it cannot be recovered by multiplying a uniform entry estimate by a
terminal range-ball cardinality.  The direct generated-precision row is an
input to this gate, but does not by itself prove the three-term identity.

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

There are two distinct algebraic layers before the finite-range requirement.
The diagonal-multiplier intertwiners with restriction and zero extension are
unconditional: `finitePiLpScalarMultiplier_comp_extendZeroZeroCLM` and
`restrictZeroCLM_comp_finitePiLpScalarMultiplier` prove that both sides vanish
identically off the regional carrier.  Support becomes essential only when the
ambient projector `E R` is inserted, through the separately named theorem
`cmp99RegionalSquareMultiplier_comp_regionProjector` and its premise
`CMP99RegionalSquarePartitionSupported`.  Thus compression of the commutator
itself must not carry a redundant support hypothesis, while an ambient inverse
sandwich that inserts `E R` must cite the support theorem explicitly rather
than hide it in `simp`.  No finite-range premise is used in either exact
algebraic layer.  The later analytic estimate is stronger.  To prove sparsity
of consecutive correction factors and make the regional defect contractive,
the physical specialization must expose a collar condition of the form

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

### Source scale gate for the `O(M^-1)` factor

The primary text on printed p. 408 makes the scale separation explicit.  Its
large blocks have side `M * L^(j eta)`, while the local operator range is on
the `L^(j eta)` scale; it assumes the large-block parameter `M` is sufficiently
large (more precisely it writes `M = K R0 M0`).  This ratio is what survives as
the `O(M^-1)` factor in (3.89).

The current generated periodic specialization must not be identified with
that source partition merely because it proves a linear cutoff slope.  It uses

```text
cutoffScale = 2 * M^(depth+1)
finiteRange =     M^(depth+1),
```

so its scale/range ratio is the fixed number `2`; composing the slope with a
finite-range or Combes--Thomas estimate cancels the displayed inverse scale
up to a constant.  Thus this specialization cannot by itself witness the
source `O(M^-1)` contraction.  A source-facing producer must retain an
independent large-block/localization factor (equivalently, a factorization of
the ambient torus by the larger cutoff spacing) and derive the active-cell
overlap from that same partition.  Until that dictionary is present, a green
slope or overlap module is algebraic infrastructure, not attainment of the
regional defect window.

The tree already contains the correct scale *shape* in
`cmp99SourceGeneratedSmoothCutoffScale M depth = M^(depth+2)`, exactly one
factor `M` above the certified range `M^(depth+1)`.  What remains is not to
postulate its slope, but to construct the exact periodic square partition and
ambient-torus factorization at that scale and then transport the same derived
overlap theorem to it.

The overlap cost is not a second constant at this larger scale.  It is
derived from the same CMP95 profile support: at most two active translates
per coordinate and hence at most `2^4 = 16` active source cells in four
dimensions.  The source-facing specialization must prove this for the
large-block partition itself rather than import an independent overlap datum
from the auxiliary terminal-scale partition.

The active-window coordinate is itself scale-sensitive.  The rescaled cutoff
at physical coordinate `x` is definitionally the periodic cutoff at `x / M0`;
therefore its active cells live in
`cmp95PeriodicTensorActiveCellWindow Q (fun i => x i / M0)`, now exposed as
`cmp95RescaledPeriodicTensorActiveCellWindow Q M0 x`.  Reusing the unscaled
window at `x` is not a harmless change of notation: it changes the residue
classes and was rejected by the fresh-clone overlap gate.

The source-scale implementation also records three local elaboration rules
learned from the failed pre-validation passes.  First, normalize natural casts
in the direction demanded by the goal: `((M ^ n : ℕ) : ℝ)` and
`(M : ℝ) ^ n` are propositionally equal but Lean may require the cast lemma
in one specific orientation.  Second, unfold dependent scale abbreviations
from the outer definition inward; unfolding the inner abbreviation first may
cause the outer one to reappear and defeat an otherwise trivial `ac_rfl`.
Third, when `simp` does not rewrite a coordinate expression below a function
argument, prove the corresponding equality of functions by `funext` and
rewrite with that equality explicitly.  These are elaboration conventions,
not source estimates and not discharged mathematical obligations.

For the regional defect, the relevant overlap is the literal source-side
one.  Every summand has the ordered form

```text
[h_Pi, Delta'] G'_Pi h_Pi.
```

Applied to a one-site probe at `source`, the rightmost multiplier makes that
summand exactly zero unless `h_Pi(source) != 0`.  The cell sum is therefore
restricted to the same at-most-sixteen active cells before either Schur sum
is taken.  No second overlap parameter, and no independently postulated
overlap of a finite-range enlargement of the supports, is needed.  The
finite-range collar remains a separate geometric input for the common
ambient/Dirichlet locality dictionary; it is not an overlap surrogate.

The analytic composition must also retain the source scale in the right
order.  First establish a normalized weighted-row budget `B_Delta` for the
literal precision.  The commutator then retains that row budget and pays only
`slope * finiteRange`, the certified `O(M^-1)` quantity.  It must not recreate
the precision row from a uniform entry bound times the cardinality of the
range ball: the normalized `Q'^* Q'` mass cancels its block volume, while that
crude reconstruction would reintroduce a power of the terminal range and can
erase the gain completely.

The commutator row composes directly with a weighted row for the exponentially
localized Dirichlet Green, without loss of spatial rate.  Converting the
commutator separately to an exponential kernel would spend an avoidable
factor `1 / rate`; rebuilding either row from pointwise decay would spend an
additional shell or ball factor.  The source-facing defect budget must retain
the schematic form

```text
overlap * (slope * finiteRange) * B_Delta
        * (2 / coercivity) * greenShellSum,
```

with `slope * finiteRange = O(M^-1)` established before the composition.
The currently available
`cmp99SourceGeneratedPhysicalPrecision_weightedRowKernelBound` is not yet the
required producer: it is derived from an entry bound and a range-ball
cardinality.  The missing physical input is a direct row estimate for the
normalized Laplacian-plus-`Q'^*Q'` precision.

The source tree already fixes the normalization needed for that direct mass
row.  For one scale,
`cmp99SourceTransportedBlockAverageCLM_single` contributes one literal
`cmp99SourceBlockAverageWeight M d = M^-d` on the averaging side, while
`cmp99SourceTransportedBlockWeightedAdjointCLM_eq_smul_adjoint` identifies the
counting-space adjoint with the synthesis coefficient that contributes the
second copy.  Summing the resulting `Q^* Q` row over the `M^d` sites in its
owner block therefore leaves exactly one factor `M^-d`, rather than a block
cardinality.  The source-faithful producer should iterate this identity along
`generatedCountingMass`, yielding the explicit *unweighted* row amplitude
`(cmp99SourceBlockAverageWeight M d)^depth` (and then use
`generatedCountingMass_eq_QprimeMass`).  At positive row rate its certified
finite range additionally costs `exp (rate * range)`, but still no block-ball
cardinality.  This recursion and its fixed-output orientation are now proved
by `cmp99SourceIteratedLift_generatedCountingMass_fixedOutputWeighted` and
`cmp99SourceIteratedLift_QprimeMass_fixedOutputWeighted`.  They were verified
in a fresh Colab clone at source checkpoint
`db04d33a19be5f4e87d842f6cc9a3925e53f4388`.  The operator-norm contraction
of `Qprime` is not used as a substitute.

There is also an orientation boundary that the source dictionary must keep
visible.  `FinitePiLpTypedWeightedRowKernelBound` fixes a source delta and
sums its image over targets.  Equation (3.88) fixes the displayed output site
`x` and sums over input sites.  Although
`cmp99SourceGeneratedPhysicalPrecision_isSymmetric` proves symmetry of the
complete physical precision, vector-valued block symmetry does not by itself
turn the two pointwise-in-vector sums into the same inequality.  The direct
source-fixed estimate is the right input for the existing delta-propagation
composition, but a claim about the literal fixed-output row of (3.88) still
requires a proved adjoint/block bridge or a separate direct estimate.

The literal complete precision now has that separate producer:
`cmp99SourceGeneratedPhysicalPrecision_directFixedOutputWeighted`.  Its
amplitude is definitionally the sum of two separately recoverable budgets:
the nearest-neighbour covariant-Laplacian row and
`|cmp99SourceGeneratedPhysicalMass|` times the normalized `Q'^*Q'` row.  This
is a direct input to the three-term identity (3.88); it does not prove that
identity, its physical cutoff slope, or the subsequent defect contraction.

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
