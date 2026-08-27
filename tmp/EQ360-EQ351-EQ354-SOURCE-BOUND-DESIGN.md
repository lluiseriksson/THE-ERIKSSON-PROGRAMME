# CMP99 (3.50)--(3.54): source-facing Eq360 bound gate

Status: design gate only. This note does not discharge a Lean obligation and
does not move `20/41` or the window-15 marker.

## Primary-source anchor

- T. Balaban, *Propagators for Lattice Gauge Field Theories in a Background
  Field III*, CMP 99 (1985), printed pp. 400--401, Eqs. (3.50)--(3.54).
- Private primary artifact: `cmp99/1103942769.pdf`, registered SHA-256
  `39F8033B35838C7BDD14F97C7FB1EDB0B35D4190B8B88F31D19D12A72D542861`.
- Visual read performed from PDF page 12 / printed p. 400 and PDF page 13 /
  printed p. 401. OCR is not authoritative for the constants below.

## Literal source decomposition

For a positively oriented bond `b`, the source uses `A'(b) = A(b)`; for a
negatively oriented bond it uses `A'(b) = R(U_b) A(b)`.  Expanding the
perturbed covariant Laplacian gives

```text
(Delta_{U'U} lambda)(x)
  = (Delta_U lambda)(x)
    - sum_{b est(x)} i ad_{A'(b)} (D_U lambda)(b)
    - i[(D_U^* A)(x), lambda(x)]
    - sum_{b est(x)} F'_{1,k}(i ad_{A'(b)}) lambda(b+).
```

The nonlinear remainder is not a caller-supplied operator:

```text
F'_{1,k}(z)
  = eta^{-2} (exp(eta z) - 1 - eta z)
  = z^2 * integral_0^1 (1-t) exp(eta t z) dt.
```

Thus the literal local perturbation of (3.52) has exactly three source
species:

1. `sum_b i ad_{A'(b)} (D_U lambda)(b)`;
2. `i[(D_U^* A)(x), lambda(x)]`;
3. `sum_b F'_{1,k}(i ad_{A'(b)}) lambda(b+)`.

The exact orientation is `Delta_{U'U} = Delta_U - V'_1(A)` as in (3.53).

### One source scale, not two independent parameters

Primary render inspection of CMP99 printed p. 400 / PDF p. 12, from the
registered primary PDF SHA-256
`39F8033B35838C7BDD14F97C7FB1EDB0B35D4190B8B88F31D19D12A72D542861`,
fixes a normalization that the earlier draft interface left too loose.  The
same source scalar `eta` occurs in all four places:

- `U' = exp(i eta A)`;
- the `eta^-2` covariant Laplacian stencil in (3.50);
- the `eta^-1` first-order term before the second equality in (3.51); and
- `F'_{1,k}(z) = eta^-2 (exp(eta z) - 1 - eta z)`.

Consequently the source-facing regrouping may not receive independent
`eta` and `spacing` parameters.  It uses `eta` definitionally both in
`cmp99Eq337PhysicalComplexPerturbedBackground U A eta` and in the two
`cmp99Eq360ComplexRegionalLaplacian ... eta` terms.  An auxiliary theorem
with two scales is algebraically legitimate, but it is not the printed
(3.51)--(3.53) producer and cannot discharge this gate.  This single-scale
specialization is also what converts the matrix generator
`i * eta * A'(b)` into the printed first species `i[A'(b), D_U lambda(b)]`
and the raw exponential remainder into the printed `F'_{1,k}` without an
untracked ratio of scales.

### The derivative sign dictionary is portante

CMP99 (3.3) prints

```text
D_U^eta lambda = eta^-1 (R(U) lambda_shift - lambda).
```

The repository conventions `covariantD0CLM` and
`cmp99Eq360ComplexCovariantDifference` are the opposite differences.  This
relationship is already sealed on the real tensor in
`cmp99Eq337PhysicalRealCovariantDerivative`, whose definition is visibly
`(-eta^-1) • covariantD0CLM`.  The complex source-facing leaf records the
corresponding zero-cochain equality as

```text
D_U^eta phi = -cmp99Eq360ComplexCovariantDifference(U,eta,phi).
```

Taking the counting-Hilbert adjoint therefore fixes the source diagonal as

```text
(D_U^eta)^* A = (-eta^-1) * gaugeConstraintQCLM(U,A).
```

Accordingly `cmp99Eq351PhysicalComplexCovariantDivergence` is only the
internally constructed **unscaled** complexification of
`gaugeConstraintQCLM`.  The printed diagonal species is the separately named
`cmp99Eq351PhysicalComplexSourceCovariantAdjoint eta U A`, defined internally
as `-eta^-1` times that divergence.  The source-facing regrouping must consume
the latter.  Identifying the unscaled divergence directly with `D_U^* A`
would lose both a sign and a spacing factor; no caller-supplied equality is an
accepted repair.

### The oriented endpoint dictionary is a separate gate

The source derivative in (3.3) is defined on an oriented bond, whereas the
repository stores a complex one-cochain only on positive `PhysicalBond`s.
Moreover `ConcreteEdge.source` is the anchor of that positive bond, not the
oriented initial vertex when `sign = false`.  The source-facing derivative is
therefore constructed separately as

```text
D_U^eta phi(e) = eta^-1 (R(U_e) phi(e.dstV) - phi(e.srcV)).
```

For the canonical negative edge leaving `x`, namely
`ConcreteEdge.mk (x.shiftBack i) i false`, this becomes

```text
eta^-1 (R(U(x,x-eta e_i)) phi(x-eta e_i) - phi(x)).
```

The named Lean object is
`cmp99Eq351PhysicalComplexOrientedSourceCovariantDifference`; its positive
branch is definitionally the positive-bond derivative and its negative branch
is a separately stated theorem using `srcV`/`dstV`.  At nonzero spacing the
named transport identity reconstructs `R(U_e) phi(e.dstV)` from this
derivative.  The (3.51) regrouping must cite that identity on both branches.
It may not use `ConcreteEdge.source` as the oriented source, and it may not
specialize the positive-bond formula by renaming the anchor.

There remains one explicit source-consistency check before the printed
diagonal sign may be sealed.  The raw stencil expands the exponential with
the repository commutator order, while printed (3.51) writes both
`i ad_{A'(b)} D_U phi(b)` and `i[(D_U^* A)(x),phi(x)]`.  The proof must expose
the precise matrix definition of `ad` and derive the diagonal sign from the
already fixed equality
`D_U^* A = -eta^-1 * gaugeConstraintQCLM`; a `ring` proof over an unnamed
commutator is not accepted.  If the two conventions disagree, that is a
source-dictionary no-go, not permission to flip the adjoint or the oriented
one-cochain silently.

The visual re-audit makes that gate concrete.  Printed (3.8) defines
`D_U^* A` as transported incoming minus outgoing, while printed (3.51)
places `-i[(D_U^* A)(x),phi(x)]` in the Laplacian expansion (equivalently
the positive diagonal species in `V'_1`).  The repository's proved oriented
sum is outgoing minus transported incoming.  Substituting only these named
equalities into the raw commutator expansion therefore currently appears to
give the opposite diagonal sign.  This is an observed source-consistency
question, not yet a compiler theorem.  Before the three-species producer is
written, a standalone matrix-level lemma must either derive the printed sign
from the exact `ad` convention or seal the mismatch as a source-dictionary
no-go.  Changing the already fixed derivative, adjoint, or negative-edge
definitions to make the final display close is not an accepted repair.

The convention itself is no longer an open interpretive escape.  Earlier on
the same primary text CMP99 defines `R(U) X = U X U^-1`, and (3.50) rewrites
the perturbed transport as
`R(exp(i eta A')) = exp(i eta ad_{A'})`.  Differentiating this identity at
zero fixes `ad_A X = A X - X A`, exactly the repository order.  With the
canonical negative-edge perturbation required by inverse-link
factorization, the oriented sum is `-eta * D_U^* A`; hence the raw term
`-eta^-2 [i eta A', R(U) phi]` contributes
`+i[(D_U^* A)(x), phi(x)]`, not the minus sign printed in (3.51).  The next
artifact is therefore a standalone matrix-level sign no-go (plus an
explicit noncommuting witness), followed by a source-dictionary decision.
Until that artifact has a compiler/axiom verdict, neither printed sign is a
producer and no Eq. (3.51) regrouping may be promoted.

This exact-sign no-go does not by itself invalidate the quantitative endpoint
(3.54): the canonical raw term and the printed term are negatives of one
another, hence have equal pointwise matrix norm.  The no-go artifact also
records that norm equality.  After it is compiler-verified, the source-facing
route may use the corrected raw sign for the exact regrouping and the proved
norm equality for the printed absolute estimate; it may not cite (3.51) as an
exact identity with the printed diagonal sign.

## Printed quantitative endpoint

Let `ell = L^j eta`. Under the source domain (3.37), printed Eq. (3.54) is

```text
|(V'_1(A) lambda)(x)|
  <= 4 d alpha1 ell^{-1} |nabla_U lambda|
     + 2 d alpha1 ell^{-2} |lambda|
     + 8 d alpha1^2 ell^{-2} |lambda|.
```

The norms on the right involve only nearest neighbours of `x`.

## Lean acceptance gates

1. Do not triangle-bound the current three raw stencil differences.  First
   prove the literal (3.51)--(3.52) regrouping, including the diagonal
   `D_U^* A` term and the internally constructed exponential remainder.
2. The producer must consume the already named Eq337 physical complex domain
   clauses, not replace them with fresh bounds:
   `CMP99Eq337PhysicalComplexAmplitudeBoundOn` and
   `CMP99Eq337PhysicalComplexCovariantDerivativeBoundOn`.
3. The positive/negative bond dictionary for `A'` is a theorem, not a free
   family.  The negative branch must use the same source transport `R(U_b)`
   as the Laplacian stencil.
4. The constants `4 d`, `2 d`, and `8 d`, together with the powers
   `ell^{-1}` and `ell^{-2}`, remain visible in the theorem statement.
5. A coordinate/matrix norm conversion may expose chart budgets, but it may
   not rename the source bounds.  If both directions are required, define and
   audit both operator-norm budgets explicitly.
6. Only after the pointwise source theorem is proved may it be transported to
   the finite-range/output-fixed or owner-weighted norm consumed by the
   Eq360 precision perturbation and the window-15 chain.
7. Keep the all-`eta` raw identity and the printed nonzero-spacing identity
   separate.  The latter consumes the existing `eta_pos` field of
   `CMP99Eq337PhysicalComplexPerturbationDomain`; it must not be stated for
   `eta = 0` or receive an unrelated nonzero-spacing witness.

## Current boundary

The existing Eq360 PRE-VALIDATION drafts prove the exact difference of the
two analytic regional Laplacians and the four-term precision algebra.  They do
not yet prove the source decomposition above, the (3.54) pointwise bound, or
its downstream operator-norm transport.

The aggregate proposition
`CMP99Eq337PhysicalComplexPerturbationDomain`, the oriented perturbation and
the two exponential-adjoint remainder modules are now sealed by exact cold
evidence at source `77c0e4834ce69d8b174d37aeefac56fd5b06b5ad` and seal
checkpoint `a5e4d03bbf6fd237fa60d1735ffa442203e791bf`.  The next source-bound
gate may consume those named declarations, but it may not replace their
amplitude and covariant-derivative clauses with fresh bounds.

### Static re-audit after the Eq. (3.51) remainder seal

`tmp/EQ360-COMPLEX-PHYSICAL-COMPILER-GATE-DRAFT-PATHS.txt` is an inventory
of auxiliary algebra drafts, not the next promotable source gate.  In
particular, the current local-Laplacian draft still receives independent
`U0 U1`, its expanded stencil does not expose the named diagonal
`D_U^* A` species, and its so-called source perturbation does not specialize
the sealed exponential-adjoint remainder at the canonical oriented physical
field.  Wrapping those objects in `CMP99Eq360ComplexClosedPhysicalInput` does
not turn the raw stencil difference into the printed (3.51)--(3.54)
decomposition.

Consequently none of those ten drafts may be promoted as a source-facing
producer until compiler-facing modules 3--5 below exist and consume the
already sealed Eq. (3.37) domain and Eq. (3.51) remainder declarations.  A
green compile of the old ten-path inventory would certify only the auxiliary
operator algebra and would not advance the source-bound gate, `20/41`, or
window 15.

## Compiler-facing module split

The next implementation is finite and should preserve the following phase
boundaries.  Provisional filenames are descriptive; changing a filename does
not change the gates.

Before module 3 below is promotable, the analytic stencil itself has one
explicit prerequisite gate.  The scratch files
`BalabanCMP99Eq360ComplexRegionalLaplacian.draft` and
`BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice.draft` are not theorem
inputs: they must first become ordinary `YangMills/RG` source/audit pairs and
pass a fresh compiler/axiom gate.  The real-slice proof must consume the
sealed Eq. (3.59) real-slice dictionary; it may not assume equality with the
physical Dirichlet Laplacian.  Separately, the multiplicativity and positive-
bond factorization gate at source checkpoint
`7e30329353488c0937aa578088d9939c6ac8f591` remains PRE-VALIDATION until its
own cold evidence exists.  Its repinned runner is checkpoint
`3232c8a6a3ea146a2e6ed2ddfc868c0e27ddb5ee` with SHA-256
`C3BC0365C449A7205A4C19E05D765663EBF8306B86AC53CE50092AAF1CC60996`;
the notebook vehicle is checkpoint
`257271b220acf805ed578b6b7603bede2a745b3c` with SHA-256
`B3A77812FBE50A00DE3F2B50C59DDA7D266F8A4EDD9F37F15268B80ECBE4BBF9`.
Thus the dependency order is literal regional
stencil -> real-slice dictionary -> adjoint composition/positive-bond
factorization -> source regrouping.  A green prefix does not certify a later
arrow.

1. `BalabanCMP99Eq351ExponentialAdjointRemainder`: define the nonlinear
   remainder internally as `exp(Y) X exp(-Y) - X - [Y,X]` and prove the exact
   algebraic decomposition.  This leaf has no physical input and does not
   claim the quadratic norm bound; the physical use of that bound remains a
   named obligation of the source-facing pointwise producer.
2. `BalabanCMP99Eq351ExponentialAdjointRemainderBound`: derive the literal
   `8 * ‖Y‖^2 * ‖X‖` bound from the internally constructed remainder under
   `‖Y‖ ≤ 1/4`.  The physical substitution and the Eq. (3.37) amplitude
   clause are not inputs to this generic algebra leaf.
2a. `BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion`: combine the
   canonical positive-bond factorization with the exact exponential-adjoint
   identity at matrix level.  Its endpoint constructs the baseline-
   transported field, the named generator `i eta A'(b)`, its commutator and
   its nonlinear remainder internally.  This is a PRE-VALIDATION algebraic
   subleaf of module 3, not the three-species regional regrouping and not a
   pointwise bound.  It is staged at checkpoint
   `b2d482fa40fe1324ae643cec429c8f6f82d82e55` for retained-runtime diagnosis;
   no later module may cite it as sealed before a compiler/axiom gate.
   This positive-edge leaf does not by itself rewrite the backward term of
   the regional stencil.  Module 3 must also prove the canonical negative-
   edge factorization
   `U'_b = exp(i eta A'(b)) U_b` for the internally constructed oriented
   `A'`, using `gaugeConfigOfPositiveBonds_apply_neg` and the same background
   transport as
   `cmp99Eq351PhysicalComplexOrientedPerturbation_neg`.  That factorization
   is a theorem/sublemma of the regrouping path, not a caller-supplied
   equality and not a consequence silently attributed to the positive case.
   The same leaf exposes the backward-stencil form as a theorem: the inverse
   of the canonical perturbed positive link is rewritten, by the gauge-config
   reversal law, to the oriented negative exponential times the compact
   negative link.  Module 3 may cite that result; it may not receive the
   inverse-link equality as an input.
2c. `BalabanCMP99Eq351PhysicalComplexCovariantDivergence`: construct the
   printed complex zero-cochain derivative and prove that it is the negative
   of the Eq360 repository difference.  Construct the unscaled backward-
   divergence stencil from the same physical background and one-cochain, and
   identify it with the sum of the canonical outgoing and incoming oriented
   values of `A'`.  In the same leaf construct the printed source adjoint
   internally as
   `cmp99Eq351PhysicalComplexSourceCovariantAdjoint eta U A =
   -eta^-1 • cmp99Eq351PhysicalComplexCovariantDivergence U A`.  The scratch
   source/audit pair is PRE-VALIDATION in `tmp`; it has no `.olean` or axiom
   verdict.  This leaf removes the possibility of a caller-supplied diagonal
   field while preserving the printed sign and spacing, but it does not prove
   the three-species Laplacian identity or any Eq. (3.54) bound.

   Its source-facing real-slice dictionary is fixed as a theorem, not an
   implicit identification.  For a real physical one-cochain `A` it must
   identify the complex divergence with
   `cmp99SUNLieCoordComplexificationLM Nc
   (gaugeConstraintQCLM (matrixSUNAdjointModel Nc) U A x)`.  This follows
   pointwise from the already sealed real-slice theorem for the canonical
   oriented perturbation and the literal backward-divergence stencil.  The
   regional adjoint theorem
   `cmp99ActiveRegionSourceCovariantD0CLM_adjoint_apply` instead audits the
   repository derivative convention: it is the same unscaled bracket after
   restriction to the active carrier and multiplication by `spacing⁻¹`.
   Because the printed derivative (3.3) is the negative of that repository
   derivative, the printed adjoint has the additional visible minus sign.
   The regional theorem is therefore not the definition of the source
   complex diagonal species and cannot justify dropping that sign.  No bridge
   module is staged until the PRE-VALIDATION divergence pair itself has a
   compiler/axiom verdict.

3. `BalabanCMP99Eq351ComplexLaplacianRegrouping`: construct `U1` with
   `cmp99Eq337PhysicalComplexPerturbedBackground U A eta`, expand the literal
   regional stencil, and prove the three-species identity.  The nonlinear
   exponential remainder is the specialization of module 1 at the same
   positive-bond exponential.  This module has no norm hypotheses.  Its
   algebraic prerequisite is the existing PRE-VALIDATION leaf
   `BalabanCMP99ComplexSpecialLinearAdjointComposition`, which must be
   promoted and audited rather than reproved inside the regrouping.

   The source-facing theorem signature is fixed before implementation.  Its
   data are only `Omega`, the compact physical background `U`, the physical
   complex one-cochain `A`, the single source scale `eta`, the Dirichlet
   field and its active site.  It must instantiate the two analytic
   backgrounds as
   `cmp99PhysicalGaugeBackgroundToSpecialLinear U` and
   `cmp99Eq337PhysicalComplexPerturbedBackground U A eta` inside the
   statement, and both regional Laplacians must use that same `eta` as their
   spacing.  The existing auxiliary local-perturbation operator with free
   `U0 U1` may be used only after those substitutions; it is not itself the
   source producer.  Likewise, the oriented `A'`, the diagonal
   `cmp99Eq351PhysicalComplexSourceCovariantAdjoint eta U A`, and the
   exponential remainder are named internal expressions.  The unscaled
   divergence remains visible only through its proved definition of that
   source adjoint.  No equality identifying any of them with caller data is
   an accepted premise.  The first endpoint is a pointwise three-species
   equality; an operator wrapper, if useful, is derived from that equality
   rather than used to hide it.

   The cancellation of the two spacing factors is not valid at `eta = 0`.
   Indeed, at zero the two regional Laplacians coincide while
   the printed linear and diagonal species need not vanish.  The compiler
   module must therefore expose two layers: a raw exact identity, valid for
   every `eta`, in which the factors `eta⁻¹ * eta` remain visible; and the
   printed (3.51)--(3.53) corollary, which consumes `eta_pos` (or its derived
   `eta_ne`) from the already named Eq. (3.37) source domain.  It may not add
   a fresh smallness or normalization premise, and it may not silently use
   the zero parameter of the auxiliary baseline constructor to justify the
   cancellation.

   The implementation order inside this module is also fixed.  First expose
   the regional Laplacian as `eta⁻¹ • eta⁻¹` times the literal two-orientation
   nearest-neighbour stencil.  Next prove one matrix adjoint expansion for
   each canonical orientation, using the positive and negative factorization
   theorems already owned by the input gate.  Only then sum the two branches,
   replace their common on-site contribution by the unscaled divergence,
   simplify the spacing factors with the Eq. (3.37) nonzero witness, and
   rewrite the result to
   `cmp99Eq351PhysicalComplexSourceCovariantAdjoint`.  This prevents the
   nested `D*D` presentation of the regional operator from hiding the
   diagonal species or its source sign/spacing, or from creating a
   caller-supplied oriented field.

   Provisional declaration boundaries (names may change, meanings may not):

   - `cmp99Eq351ComplexRegionalLaplacianStencil` and an application theorem
     exposing the two oriented neighbours at each site;
   - `cmp99Eq351PhysicalComplexOrientedAdjointIncrementMatrix_eq`, proved in
     the positive and negative canonical cases and containing the named
     exponential remainder;
   - `cmp99Eq351ComplexLaplacianRegrouping_raw`, with every spacing/generator
     factor still present and no nonzero premise;
   - `cmp99Eq351ComplexLaplacianRegrouping_of_eta_ne`, the printed
     three-species equality, with the nonzero witness supplied only by the
     source-domain wrapper.

   The first boundary is now materialized in scratch as
   `BalabanCMP99Eq351ComplexRegionalLaplacianStencil.draft`: it proves the
   all-spacing `eta⁻¹ • eta⁻¹` stencil identity and separately transports the
   inverse-positive incoming link to the canonical negative concrete edge.
   Its companion audit has four readouts.  Both remain PRE-VALIDATION; their
   presence is implementation progress, not compiler evidence.

   The second boundary is likewise materialized in scratch as
   `BalabanCMP99Eq351PhysicalComplexOrientedAdjointExpansion.draft`.  It
   performs the Boolean orientation split internally and cites the distinct
   positive and negative expansion theorems; its statement exposes only the
   canonical edge, generator and named remainder.  The same leaf defines the
   literal non-baseline increment and proves the exact subtraction theorem.
   Its three-readout audit is also PRE-VALIDATION.

   The all-spacing third boundary is materialized as
   `BalabanCMP99Eq351ComplexLaplacianRegroupingRaw.draft`: at the unscaled
   stencil level it proves that the perturbed-minus-baseline difference is
   the negative sum of the two canonical oriented increments, then lifts the
   result to the full regional Laplacians with both inverse-spacing factors
   still explicit.  It deliberately does not yet identify the commutator sum
   with the internally scaled `D_U^* A` or cancel any spacing factor, so the
   nonzero-spacing printed corollary remains open.  Its three-readout audit
   remains PRE-VALIDATION.
4. `BalabanCMP99Eq354ComplexLaplacianPointwiseBound`: consume one
   `CMP99Eq337PhysicalComplexPerturbationDomain U A eta alpha1`, region
   membership, and the regrouping theorem.  Its endpoint retains the printed
   constants `4*d`, `2*d`, `8*d` and the powers `ell^-1`, `ell^-2`.
5. `BalabanCMP99Eq354ComplexLaplacianOwnerBound`: transport the pointwise
   result to the output-fixed / owner-weighted norm used by the regional
   defect.  Any chart conversion and finite-neighbour count are named here;
   the source clauses are not renamed or replaced.
6. `BalabanCMP99Eq360ComplexSourcePrecisionPerturbation`: combine the
   Eq. (3.59) internally generated forward/starred pair with the Eq. (3.51)--
   (3.54) Laplacian producer.  This is the first module allowed to identify
   the four-term Eq. (3.60) algebra with the physical source perturbation.

The baseline and perturbed Laplacians in the four source-facing modules share
one active carrier and one spacing.  The perturbed background is definitionally the
Eq. (3.37) construction above; no equality between a caller-supplied `U1` and
that background is accepted.  Until modules 1--5 compile and pass their axiom
audits, `cmp99Eq360ComplexLocalLaplacianPerturbation` remains valid auxiliary
algebra but is not a producer of the source bound.

## Compiler inventory fixed before promotion

The first gate was deliberately smaller than Eq. (3.60).  It promoted and
audited the following eight files before any source-bound consumer was
allowed to compile:

1. the literal aggregate
   `CMP99Eq337PhysicalComplexPerturbationDomain` and its audit;
2. the canonical oriented complex perturbation `A'` and its audit;
3. `BalabanCMP99Eq351ExponentialAdjointRemainder` and its audit;
4. `BalabanCMP99Eq351ExponentialAdjointRemainderBound` and its audit.

That gate is sealed at `a5e4d03bbf6fd237fa60d1735ffa442203e791bf`.  The
domain aggregate carries the already named amplitude and covariant-
derivative predicates as fields; it does not introduce replacement bounds.
The oriented perturbation is constructed from the physical one-cochain and
the sealed background transport on each bond orientation; it is not a
caller-supplied `A'`.  The remainder gate constructs the nonlinear third
species internally and keeps the constant eight visible.  Its promotion
scope, hash gate and pinned Colab contract live in
`tmp/EQ351-EXPONENTIAL-ADJOINT-REMAINDER-COMPILER-GATE-DRAFT-PATHS.txt`,
`tmp/promote_eq351_exponential_adjoint_remainder_compiler_gate.py` and
`tmp/verify_eq351_exponential_adjoint_remainder_contract.py`.

The current regional-stencil inventory fixes the next proof boundary:

- `cmp99Eq360ComplexRegionalLaplacian` already supplies the literal analytic
  Dirichlet stencil on one carrier and one spacing;
- `cmp99Eq337PhysicalComplexPerturbedBackground_apply_pos` fixes the positive
  bond as `exp(i eta A_b) U_b`, while the already named negative-bond matrix
  theorem supplies the same oriented background rather than a second choice;
- the missing regrouping theorem must expose the source-oriented `A'` and the
  internally scaled diagonal `D_U^* A` contribution explicitly.  Neither may
  be represented by a caller-supplied one-cochain or a free diagonal
  operator, and the latter may not be replaced by the unscaled divergence.

Therefore a green compile of the existing four-term Eq. (3.60) algebra cannot
be cited as evidence for (3.51)--(3.54).  The latter becomes evidence only
after the canonical orientation dictionary, diagonal term, internal
remainder, and the printed `4*d`, `2*d`, `8*d` endpoint have all passed their
own source/audit stages.

## Materialization inventory (2026-08-27)

This inventory records implementation state, not mathematical credit:

- `BalabanCMP99Eq351ExponentialAdjointRemainder` and
  `BalabanCMP99Eq351ExponentialAdjointRemainderBound` are promoted and sealed.
- `BalabanCMP99ComplexSpecialLinearAdjointComposition` and
  `BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization` are promoted but
  remain `PRE-VALIDATION`; the Eq. (3.60) regional gate must audit them before
  either may be cited as sealed.
- The positive-adjoint expansion, negative-bond factorization and covariant
  divergence source/audit pairs are committed scratch files.  The divergence
  pair now also states the real-slice dictionary to the literal physical
  `gaugeConstraintQCLM`; it derives this from the sealed background stencil
  and coordinate complexification rather than accepting an identifying
  equality.  Their exact manifests pass the lightweight overlay-text guard,
  but they have no cold compiler or axiom verdict.
- Their six-path promotion boundary is now fixed by
  `EQ351-REGROUPING-INPUTS-COMPILER-GATE-DRAFT-PATHS.txt` and the fail-closed
  promoter `promote_eq351_regrouping_inputs_compiler_gate.py`.  The promoter
  refuses to run until all eight Eq. (3.60) regional source/audit notices have
  been sealed.  This is dependency ordering only, not compiler evidence and
  not mathematical credit.  The cold queue scope is independently fixed by
  `verify_eq351_regrouping_inputs_contract.py`: three source/audit pairs,
  twenty-eight axiom readouts and a cold root, generated only after promotion by
  `generate_eq351_regrouping_inputs_runner.py`.  The one-cell launcher,
  durable-archive verifier and six-notice selective sealer are likewise fixed
  by the corresponding `generate_*_notebook`, `verify_*_archive` and
  `seal_*_prevalidation` scripts.  None can manufacture evidence before the
  exact promoted SHA exists.
- `BalabanCMP99Eq351ComplexLaplacianRegrouping`, both Eq. (3.54) bound
  producers and `BalabanCMP99Eq360ComplexSourcePrecisionPerturbation` are not
  materialized.  They remain the finite source-facing suffix of this chain.

The fail-closed execution order is fixed before another cold run.  First seal
the already promoted adjoint-composition/positive-bond pair with its dedicated
four-file gate.  Then promote and cold-seal the ten-file auxiliary Eq. (3.60)
gate.  Only after both disjoint notice sets are retired may the six-file
regrouping-input gate be promoted.  The older combined regional runner remains
a diagnostic inventory; its eight-file sealer overlaps the regional
Laplacian notices owned by the ten-file Eq. (3.60) gate and therefore must not
be used as a second notice-removal path.  This ordering changes no theorem and
grants no mathematical credit; it prevents two evidence tools from claiming
the same PRE-VALIDATION boundary.

None of these prefix states moves `20/41`, attains window 15 or inhabits
`TermSource`.
