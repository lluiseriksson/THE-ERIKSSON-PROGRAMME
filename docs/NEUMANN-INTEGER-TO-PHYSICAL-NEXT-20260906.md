# Next R2 bridge after the seven-name integer image cold gate

## Superseding measured state, 2026-09-06

The finite-to-integer physical counting dictionary and full one-dimensional
image-family coverage are COLD SEALED at af35fbb8c (ledger1140). The literal
multidimensional rectangle family passed HOT at fbf2e61f3 (ledger1142), with
explicitly pinned subtype beta/p. Its exact-body production promotion and
five-name audit remain PRE-VALIDATION, pending the next cold cohort.
Promotion checks: Git-blob identity/text/import gates, exit0/0.1700507s,
15728640 observed RSS. An initial local checker draft accidentally omitted
its check body; missing expected output caught it before publication. That
exit0 was NOT counted as verification. The complete checker is the evidence.

Actual full (2.46) source-image summability is currently in a separate bounded
HOT run at acc09ce87, not yet a verdict; see NEUMANN-ACTUAL-FULL-GREEN-HOT-20260906.md.
The older planning/live-state paragraphs below are historical, not claims
that these already resolved steps remain open. R1/R3/R4 still remain open.
20/41,TermSource0,window15 not attained unchanged.

Design only; no compiled result or counter movement. Do not turn a common
image-indicator equality into a physical inverse by renaming its parameters.

1. Define the canonical integer representative of a finite site by
   `fun mu => ((x mu).val : Int)` and prove injectivity coordinatewise.
   This is the same representative already used in the inverse direction of
   `cmp89SourceNeumannRectangleSiteEquiv`, not a chosen site dictionary.
2. Prove its exact compatibility with `cmp99GeneratedTerminalBlockSite`:
   the integer representative of the generated owner equals
   `neumannIntegerBlockOwner ((M^depth : Nat) : Int)` of the fine
   representative. The actual generated owner definition in
   `BalabanCMP99SourceGeneratedMassRange.lean` divides natural values by
   `M^depth`; Lean4 v4.29.0-rc6 `Init/Data/Int/DivMod/Basic.lean:120`
   supplies `Int.natCast_ediv`, with proof `rfl`. No real cast or rounded
   physical coordinate is involved. The existing one-block collapse remains
   a named alternative bridge, not an additional assumption.
3. Use injectivity plus that identity to transport owner-equality iff.
   Then consume the literal
   `cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply` to express
   the actual generated counting-adjoint mass in integer-owner form. Keep
   `(cmp99SourceBlockAverageWeight M d)^(2*depth)` unchanged; do not replace
   it by the source-weighted coefficient to the power `depth`.
4. Specialize to the actual coarse region
   `cmp89SourceNeumannRectangleActiveRegion m`, with `hm` and `hfit` visible.
   Its lifted fine sides are `((M^depth : Nat) : Int) * m(mu)` by the sealed
   `cmp99IteratedLiftActiveRegion_cmp89Rectangle_eq`. A common printed image
   acts on integer representatives, not on an alleged permutation of the
   original half-open region. The source and target use the SAME `(k,branch)`.
5. Only then formulate the averaging intertwiner needed by the image sum.
   Fixed-image injectivity is not disjointness of the full image family and
   is not a summation interchange theorem. Those obligations must be proved
   separately before a right-inverse identity is claimed.

R1 literal regional precision/spacing/rectangle, R3 internally constructed
full fine-to-fine inverse, and R4 uniform physical value/derivative B0 remain
open. No compressed-Dirichlet/Neumann identification is imported.
20/41; TermSource0; window15 compatible and not attained.

## Full image-family coverage: located substrate, not yet proved here

Update2026-09-06: the one-coordinate decoder below passed exact-source HOTv3
(ledger1139). Its unchanged production promotion is in the cold cohort at
sourceaf35fbb8c, still PRE-VALIDATION until that gate passes. The remaining
multidimensional/summability statements below are design, not compiler claims.

The pinned Mathlib has `Int.divModEquiv` in
`Mathlib/Logic/Equiv/Fin/Basic.lean:371`: for positive natural period n,
`Int equiv Int * Fin n`, with inverse `(q,r) -> q*n+r`. It handles negative
integers via Euclidean division. This is a candidate existing substrate for
step5; do not duplicate it or assume full-family injectivity from a fixed-image
theorem. No new compiler evidence is claimed by this source inspection.

For a one-coordinate side m>0, decode an arbitrary integer u using period
2*m (NOT block-owner divisor B). Let q=u/(2*m), r=u%(2*m):

- 0<=r<m: original coordinate n=r, k=q, branch=false;
- m<=r<2*m: n=2*m-r-1, k=q+1, branch=true.

Both branches have 0<=n<m and reproduce the printed orbit 2*k*m+n or
2*k*m-n-1. The half-open split must be proved disjoint, including r=m and
r=2*m-1; negative q is not clipped. Conversely the reflected branch encodes
the residue 2*m-n-1 with quotient k-1, not k. The natural/int side conversion
must use positivity and the already constructed rectangle equivalence.

Coordinatewise composition can then target the full rectangular image-index
equivalence. Only after this exact bijection is proved may a summable family
be reindexed. Summability/operator interchange and the averaging identity are
separate gates; a bare reindexing theorem does not establish the Green inverse.

## Domain gate for the averaging intertwiner

Design restriction, not a newly compiled no-go: a nonzero field on the
original finite rectangle, extended by reflection/translation to all integer
images, generally is NOT square summable. Even the unreflected branch repeats
one nonzero value on infinitely many translates. Do not introduce that
extension as an isometry from the finite Hilbert space into global `l2`, or
silently invoke an operator identity whose domain requires such membership.

The candidate faithful route is pointwise: construct the reflected extension
as a function, prove the local averaging/stencil relations with their finite
sums, and justify convolution/image-sum interchanges using the actual kernel
summability. The resulting finite regional right-inverse identity can then
use finite-dimensional uniqueness. Bounded extension is not decay, and this
domain choice does not itself supply the kernel summability or physical B0.

## Exact next finite list after the cold dictionary cohort

R2a: on the literal `CMP89SourceNeumannIntegerRectanglePoint m`, construct
the coordinatewise family map
`((Fin d -> Int) * CMP89NeumannReflectionBranch d * RectanglePoint m)`
to `Fin d -> Int`, using `cmp89NeumannReflectionImage` itself. Prove its
injectivity and surjectivity by the interval theorem, with every `m mu > 0`
explicit. Do not silently replace the rectangular subtype by a function of
coordinate subtypes; prove that packaging equivalence. No new image formula.

R2b: fix an original point n. Restrict the full-family injection to `(k,b,n)`.
This is the exact injection required by `Summable.comp_injective`; the pinned
Mathlib Group.lean theorem requires completeness for the codomain (Complex
satisfies it). `Summable.prod` and `Summable.tsum_prod` from Constructions.lean
then split integer translations and the finite parity sum. No convergence
is inferred merely from bijectivity, and no factor `2^d` replaces the infinite
translation series.

R2c orientation gate: the already sealed
`summable_cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient_massUniform`
varies TARGET on an affine residue fibre with SOURCE fixed. The printed
reflection representation varies SOURCE images at a fixed target. These are
not the same theorem. Do not invoke translation invariance or adjunction to
rename them. The literal two-endpoint estimate
`norm_cmp89Eq246NormalizedPhysicalFineToFineGreen_le_massUniform` is available
for EVERY pair of endpoints, so it can directly bound source-varying terms
by the signed-l1 weight of `target-source`; establish summability via the
constructed integer displacement bijection and the sealed total-lattice
weight sum. This produces the required orientation without a physical
symmetry premise. The amplitude still carries its L,j,a,rho dependence.

R2d: after coverage/summability, construct the reflected field as a pointwise
function. For finite block averaging, the reflected local remainder changes
from r to B-1-r; unreflected r stays r. Cite a finite remainder permutation
and the exact owner-image lemma before swapping finite sums. Keep the two
normalizations separate: Q weight `(M^-d)^depth`, counting Q*Q weight
`(M^-d)^(2*depth)`. R3 regional right inverse and R4 uniform physical B0 still
need their own operator/sum identities and quantitative proofs.

## Reuse correction: generic source-image summability already exists

Static inspection2026-09-06 found a shorter R2b/R2c route. In
`BalabanCMP89NeumannRectangularPhysicalGreenInsertion.lean`, the generic
`CMP89FullLatticeGreenDecayCertificate` keeps the FULL two-endpoint kernel
and common amplitude/rate as parameters. Its generic producers
`summable_cmp89NeumannRectangularBranchFullGreen` and
`summable_cmp89NeumannRectangularFullGreen_sum` already prove the required
SOURCE-image orientation. They use the rectangular branch residue sum and
do not assume translation invariance or an inverse. Do not reprove them
using the proposed abstract `Summable.comp_injective` route above.

The physical specialization later in that file uses (2.48); it is NOT the
full fine-to-fine (2.46) Green and remains excluded from this physical route.
The reuse is only of the generic certificate and its generic theorems.
The next physical insertion must construct that certificate for the literal
`cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a`, with amplitude
`cmp89Eq246DirectedFullSolutionSumBound L j a rho` and fine rate
`rho / (L^j)`. The sealed two-endpoint mass-uniform contour bound supplies
the pointwise inequality; nonnegativity of its literal amplitude follows
by evaluation at equal endpoints, and positivity of the rate from rho>0
and L>0. No family of chosen Green kernels enters.

This is a located route, not a compiled new specialization. It retains
all amplitude/radius/central-pair/mass windows and the L,j,a,rho dependence;
it is NOT a uniform physical B0 proof. R2a full-family bijectivity remains
needed for the pointwise reflected extension and later averaging identity,
but is not an extra prerequisite of the already proved generic summability.

Prepared R2a source1db42284358feffc281d9c2d28b3dca1d26db64d uses
Mathlib `Equiv.subtypePiEquivPi`, `Equiv.arrowProdEquivProdArrow` and
`Equiv.piCongrRight`, rather than custom bijections of these packaging types.
Drafttext/import guards passed0.1491296s/14835712observed RSS; the exact Git-blob
minimal-repro extraction passed0.3917435s/16977920observed RSS, no compiler.
ReproSHA256cf6fbbb8dd4a8908aaac36bb66d012fe8974305afe913f9f9607ae8867f95076.
Five proposed audit names, no execution while the current cold cohort runs.

Prepared independently: `tmp/NeumannActualFullGreenReflectionSummabilityDraft.lean`
constructs the generic decay certificate for literal (2.46), then instantiates
the existing source-image sum and its real-part sum. Three proposed audit
names; text/import checks only (0.1276389s, 16056320 observed peak RSS), no
compiler evidence. This route does not depend on the new rectangle draft.
All strip/mass hypotheses and amplitude/rate units remain visible. It neither
revives the withdrawn (2.48) specialization nor supplies the regional inverse.

R2d reuse gate: `NeumannHalfCellBlockReflection` already constructs the
coordinatewise finite remainder reflection with `Fin.rev`, and proves its
involution and `blockSite` intertwining (ledger1126). Reuse that involution
as the finite permutation rather than introducing another reflected index.
What remains new is the arithmetic link from an arbitrary integer image
to this local remainder and the literal averaging finite-sum identity.
The old `BalabanCMP89NeumannPhysicalRealReflectionSummability` theorem is
explicitly (2.48), so its proof pattern may guide the real-part bound but
its conclusion is not the needed (2.46) specialization.

## R3 orientation/domain gate located against existing producers

The sealed `cmp99SourceFlatFullComplexPrecisionPointSourceSolution_eq_inverse_apply`
is explicitly a FULL PERIODIC box statement. Its point-source solution
solves the same finite periodic precision before inverse uniqueness is used.
It is useful substrate, but not a Neumann regional identity. Likewise the
sealed generic `cmp89CanonicalNeumannReflectionRepresentation_of_rightInverse`
constructs the image-series operator internally but still requires that
operator's right-inverse law for the SAME regional precision.

Do not replace the withdrawn (2.48) wrapper by (2.46), leave himage assumed,
and report the regional inverse as produced. The substantive remaining law
is the pointwise/finite-operator equation for the constructed reflection sum.
A finite-box Fourier result cannot silently become a continuous-momentum
full-lattice result or an arbitrary rectangular Neumann result. Any route
through finite periodization must expose those domain/geometry dictionaries;
the pointwise reflected-extension route must expose finite-sum interchanges
and the actual stencil/averaging compatibility. No new no-go is claimed here.
