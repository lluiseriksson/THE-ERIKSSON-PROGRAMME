# Step 8b.24 / C6c.8f2g - retained read-carrier containment

Status: **STATIC DESIGN ONLY**.  No theorem in this document has been
elaborated, no `.olean` has been materialized, and no axiom-oracle verdict
exists.  This document neither moves a counter nor turns f4/f5a into a source
producer.

## Source boundary

The primary render of CMP99 printed p. 408 states only

```text
Omega'_0 subset square
```

before Corollary 3.6.  It does not state that the recursively generated Lean
carrier `regions.retainedFineReadBonds` is contained in that cube.  Therefore
the existing f4 premise
`CMP99Eq335RetainedFineReadCarrierInsideRegularCube` is an intermediate
geometric debt, not a source hypothesis that may survive in the public
Corollary-3.6 constructor.

The accepted route is

```text
retained read-bond endpoints subset Omega'_0
  + printed Omega'_0 subset square
  -> retained read-bond endpoints subset square.
```

No direct caller-supplied carrier/cube inclusion is accepted at the endpoint.

## Endpoint invariant

The induction must track both endpoints of a positive physical bond:

```lean
def CMP99PhysicalBondEndpointsIn
    (S : Finset (FinBox d N)) (b : PhysicalBond d N) : Prop :=
  b.1 ∈ S ∧ b.1.shift b.2 ∈ S
```

Tracking only `b.1` is insufficient.  The literal `Ubar` pullback for `b`
uses Gamma1 in the source block, Gamma2 between source and target blocks, and
Gamma3 in the target block.  A source-active but target-inactive boundary bond
would therefore invalidate the desired containment while remaining well
typed.

The predicate is polymorphic in the lattice size `N`.  Fixing its type to a
single syntactic product `M * N'` would make the statement look correct at one
successor while preventing the induction hypothesis from applying at the tail
size.  This dependent-size defect was removed statically before elaboration.

## Finite brick list

### f2g.0 - orientation-safe edge endpoint lemma

For an oriented edge `e` of a path which stays in `S`, prove

```text
CMP99PhysicalBondEndpointsIn S (physicalBondOfEdge e).
```

The proof must split on `e.sign`.  For a positive edge the physical endpoints
are `(srcV,dstV)`; for a negative edge they are `(dstV,srcV)`.  The existing
`physicalBondOfEdge_fst_mem_blockOf_of_staysIn` proves only the first half and
cannot be used as if it controlled the target.

### f2g.1 - exact two-block straight-path geometry

If `x ∈ blockOf M N' y`, every edge of
`cmp99SourceParallelTransportPath x mu` has both physical endpoints in

```text
blockOf M N' y union blockOf M N' (y.shift mu).
```

This is the only nontrivial arithmetic brick.  It must use the literal edge
index supplied by `mem_cmp99StraightPositivePath_edges_exists`.  For
`k < M`, the sites `shift^[k] x` and `shift^[k+1] x` lie in the source or the
single forward target block, including at the periodic seam.  A proof merely
iterating `blockSite_shift_eq_self_or_shift` is not enough unless it also
proves that at most one coarse-face crossing occurs in the first `M` steps.

The preferred intermediate statement is a block-owner dichotomy for every
`k <= M`:

```text
blockSite M N' (shift^[k] x) = y
  or
blockSite M N' (shift^[k] x) = y.shift mu.
```

Its proof should expose the internal offset of `x` via
`cmp99BlockOffsetOfMem`, use `iterShift_apply_self`/`iterShift_apply_ne`, and
split the periodic wrap explicitly.  The result is a geometric theorem, not a
new containment hypothesis.

A bounded diagnostic over every `1 <= M,N' <= 12`, every coarse coordinate,
every internal offset and every `0 <= k <= M` checked 56,784 one-dimensional
instances (including `N'=1` and every periodic seam) and found zero
counterexamples.  Runtime was 420 ms.  This is falsification evidence only;
it is not a proof and does not change the PRE-VALIDATION status.

### f2g.2 - one-bond Ubar carrier containment

Assume both coarse endpoints of `b` lie in the active coarse region:

```text
b.1 ∈ (cmp99ActiveCoarseRegion Omega).sites
b.1.shift b.2 ∈ (cmp99ActiveCoarseRegion Omega).sites.
```

Then every bond in `cmp99SourceUbarFineReadBonds b` has both endpoints in
`Omega.sites`:

- the base path and Gamma2 use f2g.1 and the two complete-block inclusions;
- Gamma1 uses `cmp99BlockContainedContourSystem_staysIn` in the source block;
- Gamma3 uses the corresponding `concreteCMP99BlockContour.staysInBlock` in
  the target block;
- `mem_cmp99ActiveCoarseRegion_sites_iff` supplies the two complete-block
  inclusions.

The totalized off-source branch of Gamma3 is unreachable because the carrier
biUnion indexes `x ∈ blockOf M N' b.1`; the proof must eliminate that branch
from this membership fact rather than assume locality of the total function.

### f2g.3 - transported-average carrier containment

For every bond in `cmp99SourceTransportedAverageFineReadBonds Omega`, prove
both endpoints lie in `Omega.sites`.  Unpack the two `biUnion` memberships,
apply `cmp99BlockContainedContourSystem_staysIn`, then f2g.0, and finish with
the complete-block inclusion carried by the active coarse site.

### f2g.4 - recursive retained-carrier endpoint induction

Prove by induction on `CMP99SourceActiveRegionChain`:

```text
forall q in regions.retainedFineReadBonds,
  CMP99PhysicalBondEndpointsIn Omega.sites q.
```

- `stop`: the carrier is empty.
- `step`, head union: f2g.3.
- `step`, pulled-back tail: the induction hypothesis gives both coarse
  endpoints in `cmp99ActiveCoarseRegion Omega`; f2g.2 transports them through
  the literal selected-family `Ubar` carrier.

This is the point where a source-only invariant would fail: Gamma3 needs the
tail bond's target coarse block.

### f2g.5 - discharge the f4 intermediate premise

Given the source dictionary equality identifying the head region with
`Omega'_0` and the printed inclusion `Omega'_0 subset W.cube.carrier`, compose
f2g.4 pointwise to construct
`CMP99Eq335RetainedFineReadCarrierInsideRegularCube`.  This theorem, not the
raw inclusion as a caller input, is what f4/f5a may consume in the eventual
public constructor.

## Acceptance gates

1. Both endpoints are present in every invariant and public theorem.
   The endpoint predicate itself remains polymorphic in the changing lattice
   size of the typed region chain.
2. The straight path is proved to cross at most one coarse face in `M` steps,
   including the periodic seam.
3. Gamma3's totalization branch is eliminated from actual carrier membership.
4. No `fineSmall`, global background equality, arbitrary carrier inclusion or
   desired operator equality is introduced.
5. The final composition cites the printed `Omega'_0 subset square`; it does
   not claim that p. 408 directly mentions the Lean read carrier.
6. Promotion requires focal elaboration plus explicit axiom audit; this static
   document alone is not evidence.

## Static adversarial proof pass (2026-08-18)

The endpoint draft was checked against the tracked definitions of
`ConcreteEdge`, `physicalBondOfEdge`, `srcV`/`dstV`, the positive straight
path and the three Ubar contours.

* `physicalBondOfEdge` forgets the orientation bit but retains the stored
  positive-bond base.  Therefore the negative-edge branch must use `hstay`
  in reversed order: `dstV` proves membership of the stored base and `srcV`
  proves membership of its positive shift.  The draft does this explicitly.
* A straight-path edge has `k < M`; its target endpoint is the `(k+1)`
  iterate and hence uses `k+1 <= M`.  Because the internal offset is below
  `M`, those endpoints cross at most one coarse boundary, including at the
  periodic seam.  This is why the exact carrier is the union of two adjacent
  blocks rather than an arbitrary neighbourhood.
* Gamma3's totalized branch is eliminated only after recovering the actual
  `x in blockOf ...` witness from the `Finset.biUnion`.  The return path then
  uses the named `StaysIn.symm` theorem, so its endpoints are swapped rather
  than identified.
* In the recursive step, the induction hypothesis supplies exactly the two
  active-coarse endpoint memberships required by the selected-family Ubar
  theorem.  No quotient, injectivity premise or free carrier map appears.

No semantic orientation or periodic-seam defect was found by this pass.  It
is not a Lean verdict.  The first focal may still expose mechanical
elaboration errors at `Nat.div_eq_of_lt_le`, the order of
`Nat.mod_eq_of_lt` rewrites, `Function.iterate_succ_apply'`, proof
irrelevance in `dif_pos hx`, or dependent induction over the region chain.
Those are the currently named repair sites; no fallback may weaken the
endpoint statement or accept a containment premise from the caller.

## Current conclusion

The scratch endpoint pair
`BalabanCMP99SourceRetainedCarrierEndpointGeometry.draft.lean` and its audit
writes f2g.0--f2g.4 as ten declarations.  In particular it includes the
orientation-safe reversal lemma for Gamma3, the selected-family Ubar theorem,
and the recursive retained-carrier induction.  Its source SHA-256 is
`3641D88103557D1D43A40DBEC3CF1962C0C2AAB2128C41B3E312DB4D6B1FF1AF` and
its audit SHA-256 is
`5AC9DACF229E274B3FF870BF4A0077F45CA881C337A5C3C1A2EB9C25F5C02B08`.
The ten declarations and ten audit commands match, and a lightweight textual
scan finds no `sorry`, `admit`, or axiom declaration and no late import.  This
is still only static evidence: the pair has not been elaborated or
oracle-checked.

The separate scratch dictionary pair
`BalabanCMP99Eq335SourceRegionDictionary.draft.lean` and its audit writes
f2g.5 as two declarations.  `OmegaPrime0` is a visible type parameter; the
dictionary stores separately `head region = OmegaPrime0` and the literal
printed premise `OmegaPrime0.sites subset regular cube`.  It does not store the
desired retained-carrier conclusion.  Its source SHA-256 is
`74DE39D22423FFE4169ABC16085AAE3F678B4E67F2E6436F928BB6AD5AF08A64`
and its audit SHA-256 is
`0EA35D15DC77EB92D3A01D6A2EC8D196DF2038578CB1B00013B0141343B5702E`.
The two declarations and two audit commands match and pass the same textual
gates only.

Thus f2g.0--f2g.5 are now written, but none is compiler-verified.  The
definitions do not exhibit a counterexample: the exact retained carrier is
structurally compatible with the two-endpoint induction and with the printed
Corollary-3.6 premise.  Until the whole overlay is elaborated and audited, the
f4 `hinside` premise remains open and may not be described as discharged.
