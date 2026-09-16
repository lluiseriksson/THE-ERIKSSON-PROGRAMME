# C6d Eq. (3.42) physical depth-split wrapper

Static design checkpoint only.  This file is not Lean/Lake evidence and does
not change `20/41`, `TermSource = 0`, or window-15 attainment.

## Fixed nonempty carrier

The next source-facing wrapper must not accept either

- `root : ActiveGaugeRegion.Site OmegaSource`, or
- an arbitrary `[Nonempty (ActiveGaugeRegion.Site OmegaSource)]`.

Its source index is a literal
`Z0 : CMP116SourcePhysicalLocalizedRegion Dict`.  Therefore
`Z0.2` is the nonemptiness proof for
`cmp116SourcePhysicalLocalizedCoordinates Dict Z0.1`, and the active region is
definitionally the one whose sites are

`cmp116RegionSites
  (M := cmp99SourceSeparatedLargeBlockSide L K depth)
  (N' := 2*Q) Z0.1`.

Here `cmp99SourceSeparatedLargeBlockSide L K depth = K*L^(depth+1)`.
The factor `K` belongs to the physical block size `M`; it must not be moved
into `N'`.  Although both placements can give the same total ambient product,
they give different raw block carriers and therefore different localization
geometry.

The instance required by `CMP99Eq342SourceLocalizedGreenCertificate` must be
constructed internally by the named theorem
`nonempty_cmp116SourcePhysicalLocalizedActiveRegion`.  This is the physical
consumer of the Green-owner gate.  Choosing a root with `Classical.choice`
is permitted only after that theorem has supplied the instance; it is not a
caller-visible input.

## Depth split

The positive and base branches have genuinely different source data and must
remain separate.

- `depth > 0` uses
  `cmp99Eq360C6dSourceSeparatedAmbientGreen_perDepthCertificate`, the retained
  C6d regularity class, physical spacing `L^(depth+1) * eta`, and the positive
  Poincare/coercivity producer.
- `depth = 0` uses
  `cmp99Eq360C6dSourceSeparatedAmbientGreen_zeroDepthCertificate`, the literal
  base background, spacing `spacing`, and the zero-depth full-companion
  coercivity producer.

The first implementation therefore consists of two branch-specific physical
wrappers, each eliminating its caller-visible `root`.  A later single-family
dispatcher, if required by the consumer, must take a genuinely dependent
branch-data object and prove its result by cases on `depth`.  It may not fake
one common list of source inputs: the positive branch carries the retained
regularity/dictionary data, whereas the base branch carries
`background`, `chain`, and `fineSmall`.

Neither wrapper may coerce the base branch through a false `0 < depth`, nor
may it multiply the base spacing by another RG block length.

## Exact branch boundary

For both wrappers, define the literal regional carrier from `Z0` with

`M := cmp99SourceSeparatedLargeBlockSide L K depth` and `N' := 2*Q`,

then obtain its `Nonempty` instance from `Z0.2`.  The positive wrapper invokes
`cmp99Eq360C6dSourceSeparatedAmbientGreen_perDepthCertificate`; the base
wrapper invokes
`cmp99Eq360C6dSourceSeparatedAmbientGreen_zeroDepthCertificate`.  The
`root` argument required by those lower-level assemblers is selected
internally from the derived instance and must disappear from the public
signature.

The fact that the lower C6d construction factors the same ambient size as
`L^(depth+1) * (2*(K*Q))` does not license changing the raw localized carrier.
The size equality is already named
`cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier`, and the exact
site/region transports are
`cmp99Eq360C6dSourceSeparatedAmbientSiteEquiv` and
`cmp99Eq360C6dSourceSeparatedAmbientRegion`.  The wrappers must cite that
chain at the operator boundary; it is not a redefinition of `Z0`.

## What this wrapper may conclude

The depth-split wrapper may return the exact per-depth certificate with the
branch's explicit amplitude and rate.  It must not claim one common physical
`B0` or `delta0` merely by packaging those values in a dependent family.

The subsequent uniform bridge must instead exhibit fixed scalars
`B0 > 0` and `delta0 > 0` and prove, for every physical depth, the four literal
dominances needed to weaken the branch certificate to those same scalars.
That is item 7 and the first possible window-15 attainment point.

## Flat uniform bound is not the C6d certificate

The sealed theorem
`exists_cmp99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0`
does produce one positive strip radius and one point-source coefficient for
all depths.  Its operator, however, is the literal flat source-flow Green
with `QprimeStar`; it is not the non-flat canonical regional inverse appearing
in `CMP99Eq342SourceLocalizedGreenCertificate`.

Consequently item 7 may use that theorem only after a source-specific bridge
has done one of the following:

1. constructed the C6d regional Green from the flat Green by the physical
   defect/Neumann series and transported the owner bounds with its attained
   contraction; or
2. proved a literal equality between the two operator expressions from the
   same precision and inverse uniqueness.

An arbitrary equality, a caller-supplied Green dictionary, or direct reuse of
the flat `B0` against the C6d certificate is not accepted.  This is also why
the per-depth CT certificate by itself does not prove uniformity: its explicit
coercivity/amplitude/rate remain depth-dependent.

## Acceptance gates

1. The region equality is definitional or proved by a named dictionary lemma;
   no free equivalence between an arbitrary `OmegaSource` and the physical
   region is accepted.
2. Nonemptiness is obtained from `Z0.2` through
   `nonempty_cmp116SourcePhysicalLocalizedActiveRegion`.
3. Positive and zero-depth constructors are invoked in different branches.
4. No certificate, Green, inverse identity, coercivity witness, `B0`, or
   `delta0` is accepted as a caller-supplied substitute for the physical
   producer.
5. A green wrapper remains infrastructure below window 15 and does not move
   the terminal producer counter.
