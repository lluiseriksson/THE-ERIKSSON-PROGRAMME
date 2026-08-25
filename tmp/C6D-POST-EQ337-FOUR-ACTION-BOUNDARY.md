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

## First missing source-specific dictionary

After C6d.1 and the forced Eq. (3.37) background recursion, the first missing
dictionary is the two-tower Eq. (3.59) construction on the **same typed source
regions**:

```text
Q0 := Q'(U)
Q1 := Q'(exp(i eta A') U)
F2 := Q1 - Q0

Q1 = Q0 + F2
```

The source wrapper must construct `Q0` and `Q1` internally and transport `U`
and `A'` together through the cube gauge.  It may not accept `Q0`, `Q1`,
`F2`, a background family, or the displayed equality as caller data.  In the
complex continuation, the starred synthesis must be constructed
independently; it is not Lean's Hilbert adjoint of `F2` away from the real
slice.

The existing scratch definition
`cmp99Eq359PhysicalQprimePerturbation Q0 Q1 := Q1 - Q0` is only the algebraic
leaf.  It becomes source-facing only after both physical towers are internally
constructed and their real/complex gauge-covariance dictionaries are proved.

## Finite consumer chain after Eq. (3.59)

1. instantiate the literal Eq. (3.60) perturbation with the internally
   constructed `Q0`, `Q1`, `F2` and independent starred synthesis;
2. prove the exact factorization on one active source carrier before taking
   any norm;
3. build the interacting regional inverse by the source resolvent/Neumann
   route and attain the relative weighted-norm smallness theorem;
4. instantiate the value, left derivative, right-adjoint derivative and
   Laplacian action algebra for that one resulting regional Green;
5. only then combine the four amplitudes with
   `cmp99Eq342CommonAmplitude` and produce the uniform source-localized
   `(3.42)` certificate.

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
