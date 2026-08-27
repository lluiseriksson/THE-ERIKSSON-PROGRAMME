# C6d post-Eq337 boundary for the four CMP99 (3.42) actions

Status: static source/type audit only.  No Lean/Lake verdict is claimed by
this note.  It fixes the next source-specific equality that must be produced
after C6d.1 and the forced Eq. (3.37) recursion; it moves neither `20/41` nor
window 15 and does not construct a `TermSource`.

## The four already sealed fixed-depth endpoints

The per-depth assembler

```text
cmp96SourceSeparatedRegionalPrefix_eq342SourceLocalizedGreenCertificate
```

consumes exactly these four sealed action theorems:

```text
cmp96SourceSeparatedRegionalPrefixGreen_blockLocalizedSupBound
cmp96SourceSeparatedRegionalPrefixLeftDerivative_blockLocalizedSupBound
cmp96SourceSeparatedRegionalPrefixRightAdjoint_blockLocalizedSupBound
cmp96SourceSeparatedRegionalPrefixLaplacian_blockLocalizedSupBound
```

and produces one `CMP99Eq342SourceLocalizedGreenCertificate`.  All four
theorems are tied to the same objects:

```text
Omega = cmp96SourceSeparatedRegionalCell P L K Q depth cell
U     = cmp99Eq389SourceSeparatedPhysicalBackground L K Q depth Nc background
A     = cmp89SourceSeparatedAmbientPrefixPrecision ...
G     = cmp99RegionalDirichletGreen Omega A ...
```

Their scalar assembler is valid and reusable, but the four conclusions are
not yet statements about the selected Eq. (3.35) source region.

## What C6d.1 actually supplies

The prepared C6d.1 endpoint constructs, on an arbitrary printed source
region `Omega`, the literal active operator

```text
Delta'_a = Delta_{W.transformedBackground}
         + a_j * Q'_localized^* Q'_localized
```

where `Q'_localized` is generated internally by
`localizedRetainedTowerOfSourceRegion`.  It also proves:

1. the two-summand defining equality;
2. equality with the canonical presentation for the **same** transformed
   background;
3. the source-region Laplacian dictionary to the exponential representative;
4. symmetry and the exact quadratic form.

It does not construct coercivity, an inverse, an owner-decay estimate or an
identification with the separated-cell precision above.

## Direct transport is rejected

There are three independent reasons that the sealed four-action certificate
cannot be transported by `simpa`, a carrier inclusion, or a generic
restriction lemma.

1. `CMP99Eq335Corollary36SourceRegionDictionary` proves only
   `Omega = OmegaPrime0` and `OmegaPrime0.sites ⊆ C.carrier`.  It does not
   identify `Omega` with `cmp96SourceSeparatedRegionalCell ... cell`.
2. Even if `Omega` embeds in that separated cell, the inverse of a Dirichlet
   compression to `Omega` is not the restriction of the inverse on the
   larger cell.  An inclusion therefore cannot prove equality of the two
   Green operators.
3. `CMP99SourceLocalizedRetainedTower.terminalQprime_eq` compares localized
   and canonical retained prefixes for one physical background.  It is not
   the printed Eq. (3.59) comparison between the baseline tower and the
   multiplicatively perturbed tower.

Thus no theorem should be introduced whose premise is an equality between
the two independently chosen Green operators or precisions.  Such a premise
would merely rename the missing source bridge.

## Sealed Eq. (3.59) source-specific dictionary

The two-tower Eq. (3.59) construction on the **same typed source regions** is
no longer an open dictionary:

```text
Q0 := Q'(U)
Q1 := Q'(exp(i eta A') U)
F2 := Q1 - Q0

Q1 = Q0 + F2
```

The source wrapper constructs `Q0` and `Q1` internally and transports `U` and
`A'` together through the cube gauge; it does not accept `Q0`, `Q1`, `F2`, a
background family, or the displayed equality as caller data.  The complex
continuation builds the starred synthesis independently rather than using
Lean's Hilbert adjoint away from the real slice.  The physical real-slice gate
passed at source `cd6ff65638f0e09e2533733df2d7176c10714a3a`, and the retained
C6d cross-gate verified all 34 dependency-boundary blobs.  Seal
`850fd92911d0f79564718636f3f92a922b0f0e8e` retired those exact notices.

The first open source-specific dictionary is therefore C6d.1 itself: the
literal localized retained precision on the selected source region.  After
that precision is sealed, Eq. (3.60) must be instantiated on that same carrier
before any regional inverse or four-action transport can be claimed.

## Finite consumer chain after Eq. (3.59)

1. seal C6d.1, constructing the literal localized retained precision on the
   selected source region;
2. instantiate the literal Eq. (3.60) perturbation with the internally
   constructed `Q0`, `Q1`, `F2` and independent starred synthesis;
3. prove the exact factorization on one active source carrier before taking
   any norm;
4. build the interacting regional inverse by the source resolvent/Neumann
   route and attain the relative weighted-norm smallness theorem;
5. instantiate the value, left derivative, right-adjoint derivative and
   Laplacian action algebra for that one resulting regional Green;
6. only then combine the four amplitudes with
   `cmp99Eq342CommonAmplitude` and produce the uniform source-localized
   `(3.42)` certificate.

### Exact real-slice gate before item 2

The baseline in item 2 is source-selected, but it is deliberately not one
single background in both summands.  C6d.1 uses
`W.transformedBackground` in the regional Laplacian and uses the canonical
retained tower generated from
`regions.retainedFineExtension W.transformedBackground` in the `Qprime`
summand.  The generic Eq. (3.59) tower pair constructs its analytic `Q0`
recursively from one full background, while C6d.1 consumes the physical
`T.canonicalTowerAt (Fin.last depth)`.  The one-scale real-slice theorem, the
physical-contour holonomy theorem and the complex-Ubar successor real-slice
theorem are already sealed, but there is currently no source-facing recursive
assembler identifying these two terminal towers.

The assembler starts from an already sealed leaf equality, not from a new
dictionary: `cmp99Eq337PhysicalComplexPerturbedBackground_realSlice` proves
the full real-parameter identity with the canonical `SL(N,C)` image of the
physical left variation.  At `eta = 0`, the physical variation reduces to
`U`, independently of `A`, by the already audited
`cmp98PhysicalSuLeftVariation_zero`; the remaining leaf is therefore only a
named corollary of two sealed theorems, not a new analytic obligation.  No
second base background and no equality supplied by the caller are permitted.

Consequently the old scratch
`BalabanCMP99Eq360ComplexClosedPhysicalPrecision.draft` is algebraically
reusable but is not itself the C6d consumer: its single `S.U` drives both the
Laplacian and the tower, which would erase the retained-extension distinction.
Before it can be promoted, a named recursive real-slice producer must
construct the agreement between the internally generated analytic baseline
tower and the C6d canonical physical tower on the same `regions`, spacing and
retained extension.  The Eq. (3.60) wrapper must then keep the Laplacian and
averaging backgrounds as two internally constructed objects and cite the
existing read-carrier/locality theorems wherever their values are compared.
The perturbed branch has the same split: the Laplacian consumes the full
complex one-cochain on its regional read bonds, whereas the analytic `Q1`
tower must be generated from the retained extension of both the baseline
background and perturbation.  That retained complex one-cochain extension is
also an internal construction; accepting it as caller data would merely move
the dictionary into a field.
Neither the tower equality nor equality of the terminal precisions may be
accepted from the caller.  This gate moves neither `20/41` nor window 15.

There is also a model gate, not a coercible convention.  The sealed analytic
real-slice step uses `matrixSUNAdjointModel Nc` literally, whereas the C6d
regularity interface is polymorphic in `rho : SUNAdjointModel Nc`.  The
source-facing Eq. (3.60) wrapper must instantiate C6d with
`rho := matrixSUNAdjointModel Nc`; it may not accept an equality identifying
an arbitrary caller-supplied `rho` with that model.

The finite implementation order for item 2 is therefore:

1. zero-parameter corollary of the sealed analytic-background real-slice
   theorem, including the named reduction of the physical left variation at
   zero (`BalabanCMP99Eq337PhysicalComplexBaselineRealSlice` is promoted
   PRE-VALIDATION; it is not yet a sealed producer);
2. source-closed zero extension of the physical one-cochain followed by
   internal complexification, with support and norm lemmas
   (`BalabanCMP99SourceRetainedFineOneCochainExtension` is promoted
   PRE-VALIDATION; it is not yet a sealed producer);
3. recursive source-chain real-slice agreement for the analytic baseline
   tower and the C6d canonical tower at the literal
   `matrixSUNAdjointModel Nc`
   (`BalabanCMP99SourcePhysicalRealSliceTower` is promoted PRE-VALIDATION;
   it constructs both recursions and accepts no terminal equality, but it is
   not yet a sealed producer);
4. the C6d-specific Eq. (3.60) wrapper with separate Laplacian and averaging
   backgrounds, followed by its exact factorization theorem.

Only item 4 is Eq. (3.60); the preceding three are dictionaries needed to
state it without a hidden operator equality.

The generic regional compression and Neumann infrastructure in
`BalabanCMP99SourceRegionalGreenNeumann` is reusable, but its own header
already records the same boundary: the physical `Delta'_a/Q'` dictionary is
separate.  C6d.1 supplies the literal operator; Eq. (3.59) plus Eq. (3.60)
supply the first honest bridge to the interacting inverse.

## Acceptance invariant

The next public source-facing theorem may expose genuine scalar source gates,
but it must not accept any of the following as a free input:

- a preselected baseline or perturbed tower;
- `F2` or its starred partner;
- equality of regional precisions or Greens;
- a finished four-action bound;
- `B0`, `delta0`, or `norm R' < 1` under another name.

Counters remain exactly `20/41`, `TermSource = 0`, and window 15 compatible
but unattained until the corresponding compiled producers exist.

## PRE-VALIDATION implementation frontier (2026-08-27)

Eq. (3.59), its physical real slice, the 34-file retained dependency boundary
and C6d.1 are sealed; C6d.1 is recorded in ledger Addendum 949.  The live
queue is now the three promoted source/audit pairs in items 1--3 above.  Exact
source `81cc22e41d46cce150c2a263c85e4acb90087153`, runner
`300faf158314faa8c360cb4ad8527bf7e1f034a4` and notebook
`8106025057c4fac4e1e59a4e5b594f492ff1af4a` are pinned under runner revision
`c6d-next-real-slice-v3`.  The first v3 attempt is preserved as
`INCOMPLETE-RUNTIME-LOSS` after all three focal/audit pairs passed but the
cold root received `KeyboardInterrupt`; a later standard-memory runtime was
rejected by the fail-closed `HIGH_RAM_REQUIRED` preflight before checkout.
Neither incident retires a notice.  All six notices remain PRE-VALIDATION
until one fresh CPU/high-RAM focal/audit/root queue and its fail-closed
verifier pass.

The Eq. (3.51) algebra has a separate warm diagnostic PASS at source
`fab6807d1ddde2e33b5d350a14ba6dd47b61745b`.  Warm evidence is not a cold
seal and cannot retire any notice or skip the current real-slice/Eq. (3.60)
boundary.  The live frontier
therefore remains the finite chain above, with no movement of `20/41`,
`TermSource = 0`, or window 15.
