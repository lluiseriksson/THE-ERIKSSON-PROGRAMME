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

`cmp116RegionSites (M := L^(depth+1)) (N' := 2*(K*Q)) Z0.1`.

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

The wrapper is proved by cases on `depth`.  It may not coerce the base branch
through a false `0 < depth`, nor may it multiply the base spacing by another
RG block length.

## What this wrapper may conclude

The depth-split wrapper may return the exact per-depth certificate with the
branch's explicit amplitude and rate.  It must not claim one common physical
`B0` or `delta0` merely by packaging those values in a dependent family.

The subsequent uniform bridge must instead exhibit fixed scalars
`B0 > 0` and `delta0 > 0` and prove, for every physical depth, the four literal
dominances needed to weaken the branch certificate to those same scalars.
That is item 7 and the first possible window-15 attainment point.

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
