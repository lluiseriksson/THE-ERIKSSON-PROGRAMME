# Next R2 bridge after the seven-name integer image cold gate

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
