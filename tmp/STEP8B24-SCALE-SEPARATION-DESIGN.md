# Step 8b.24 — source-scale separation for the generated Fourier endpoint

Status: static design only.  No declaration in this note has been checked by
Lean, Lake or an axiom audit.

Static artifacts prepared on 2026-08-17 (all uncompiled):

* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreen.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenAudit.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexification.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexificationAudit.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrierAudit.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionary.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionaryAudit.draft.lean`
* `BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral.draft.lean`
* `BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentralAudit.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentification.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentificationAudit.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpoint.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpointAudit.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrand.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrandAudit.draft.lean`
* `BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction.draft.lean`
* `BalabanCMP99FlatComplexFibrePointSourceFourierReconstructionAudit.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpoint.draft.lean`
* `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpointAudit.draft.lean`
* `STEP8B24-PROMOTION-MANIFEST.md`

The first four cover S1 statically.  The next two cover the carrier and
transport definitions of S2a.  The following two derive the S2b precision
equality from the physical pointwise dictionary and complex linearity.  The
next pair extracts the generic noncentral fine-symbol lemma to a neutral
substrate, the following pair constructs S3 by inverse uniqueness, and the
final source/audit pair is the S4 Fourier endpoint.  The promotion manifest
fixes their dependency and validation order.  All remain uncompiled scratch.

## Question measured

The cold-sealed Gate-7 endpoint uses the diagonal specialization

```text
RG ratio                 M
fine Fourier block side  M^(depth+1)
coarse Fourier side      2*(M*Q)
total fine side          M^(depth+1) * 2*(M*Q)
```

whereas the source large-block construction uses independent scales

```text
RG ratio                 L
large-block factor       K
large-block side         K*L^(depth+1)
owner side               2*Q
total fine side          (K*L^(depth+1)) * 2*Q.
```

These are not the same physical factorization, even though their diagonal
specialization agrees at `K=L`.  Therefore Step 8b.24 must not transport the
sealed diagonal theorem by an unlabelled arithmetic cast.

## Static finding: no new generated tower is required

The underlying generated tower already has the required independent inputs:

* `cmp99SourceGeneratedFlatPhysicalGreen` is generic in the RG ratio `M` and
  coarse carrier side `N`.
* Instantiate it with `M := L` and `N := 2*(K*Q)`.
* The generic Fourier algebra in
  `BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierMode` and
  `BalabanCMP99SourceGeneratedFlatPhysicalGreenFourierSynthesis` is generic in
  the fine block side and coarse Fourier side.  Instantiate it with
  `M := L^(depth+1)` and `N' := 2*(K*Q)`.

The exact carrier identity is already sealed:

```lean
cmp99RegionalLatticeSize_sourceSeparatedLargeBlockCarrier L K Q depth :
  cmp99RegionalLatticeSize L (2*(K*Q)) (depth+1) =
    cmp99SourceSeparatedLargeBlockSide L K depth * (2*Q)
```

with

```lean
cmp99SourceSeparatedLargeBlockSide L K depth = K * L^(depth+1).
```

Thus the missing work is a source-separated realization of the existing
Step-7b dictionary and its Fourier endpoint, not a new two-scale recursive
definition.

## Existing sealed substrate

The following source-separated objects already exist and must be reused:

1. `cmp99SourceSeparatedLargeBlockSide` and the exact carrier equality above.
2. `cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q` on
   `FinBox 4 (2*(K*Q))`.
3. `cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth`.
4. `cmp99SourceSeparatedGeneratedPhysicalAmbientPrecision`, with generated
   coercivity depending on `L` and not on `K`.
5. The separated regional cutoff, slope and owner dictionaries.

The diagonal Step-7b modules remain valid algebra and evidence; they are not
the producer for the separated source endpoint.

## Finite implementation chain

The minimal parallel chain is:

### S1. Flat separated ambient Green

Construct the flat specialization of the separated ambient precision and its
Green by instantiating the already generated physical inverse at
`M=L`, `N=2*(K*Q)`, zero source radius and the canonical generated spacing.
Reindex both through
`cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth`.

Required outputs:

* separated flat ambient precision;
* separated flat ambient Green;
* both inverse laws;
* canonical complexifications and both complex inverse laws.

No regional compression or decay bound belongs to S1.

### S2. Separated Step-7b carrier dictionary

Define an active-site equivalence from the generated full active carrier

```text
IteratedLift(M=L, coarse side 2*(K*Q), depth+1)
```

to

```text
FinBox 4 (L^(depth+1) * (2*(K*Q))).
```

Compose it with the existing separated full-site equivalence to obtain

```text
FinBox 4 ((K*L^(depth+1))*(2*Q))
  ≃ FinBox 4 (L^(depth+1)*(2*(K*Q))).
```

This equivalence is the physical dictionary.  The proof must expose the two
factorizations; a bare cardinality equivalence is not accepted.

Required outputs mirror the diagonal dictionary:

* active-site, site and field equivalences;
* terminal-data complex zero-extension identity;
* transported literal Step-7b precision with
  `M := L^(depth+1)`, `N' := 2*(K*Q)`;
* equality between the complexified separated ambient precision and that
  literal Step-7b precision.

### S3. Separated generated Green identification

Transport the separated ambient Green through S2.  Prove its left inverse of
the literal full-box precision and use the existing inverse-uniqueness
endpoint.

The scalar nonvanishing theorem is already generic in `(M,N')`; instantiate
it at `(L^(depth+1), 2*(K*Q))`.  The generated stabilized denominator needs a
source-separated specialization.  It must be derived from the same generated
`a` and spacing at RG ratio `L`; it must not be accepted as an input.

Output:

```text
literal stabilized Step-7b field
  = separated generated Green ∘ literal Q'^*.
```

### S4. Separated Fourier mode and synthesis endpoint

Apply the already generic one-mode and synthesis theorems with

```text
fine block side = L^(depth+1)
coarse side     = 2*(K*Q).
```

The endpoint must retain:

* the literal fine-volume normalization/cancellation;
* the selected reciprocal fibre;
* the positive Fourier character;
* the transposed stabilized alias coefficient;
* the exact two-scale carrier dictionary from S2.

S4 is the proper input to the already drafted finite-grid aliasing and
periodic-owner estimates.  It is not yet a regional `B0` or window-15
attainment theorem.

## Named post-S4 composition (open)

S4 is not itself the owner bound.  The finite downstream composition must be
spelled out in the following order so the source-separated endpoint cannot
become an algebraic island:

1. Instantiate the Unit-E physical finite-grid aliasing theorem at
   `Kfine := L^(depth+1)` and `N := 2*(K*Q)`, with the generated `a` and the
   common physical radius.
2. Identify the normalized finite DFT in that theorem with the DFT readout of
   the S4 generated `G Q'^*` endpoint.  The selected coarse target/residue must
   be common on both sides; a sum over target-dependent readouts is not an
   accepted shortcut.
3. Instantiate the Unit-F residue-zero/owner bound with the same
   `Kfine := L^(depth+1)` and `N := 2*(K*Q)`.  Here the Unit-F variable named
   `K` is the fine localization-block side, not the independent source
   large-block parameter.
4. Transport the resulting owner metric through
   `cmp99Eq389SourceLocalizationSiteEquiv L K Q depth`, whose owner is
   literally `blockSite (L^(depth+1)) (2*(K*Q))`.
5. Only then package the source-localized Green estimate and its physical
   `B0`; regional compression and window-15 attainment remain later steps.

No new analytic estimate is predicted in steps 1--4, but each equality and
reindexing is a named proof obligation.  Three preliminary source/audit pairs
now cover the exact algebra before step 1:

* C0 fixes `ell`, `x` and `y` and identifies the S4 output multiplied by the
  inverse coarse character with the literal complete CMP89 endpoint
  integrand acting on the same fibre vector.
* C1a reconstructs one literal coarse point source as the normalized sum of
  positive Fourier modes with the inverse source character, and transports
  that identity through an arbitrary complex continuous-linear map.
* C1b composes C1a with C0, producing one normalized finite sum of literal
  CMP89 endpoint-integrand values for the generated `G Q'^*` point-source
  column.

Together they contain six public declarations and six matching audit prints
and pass the lightweight placeholder/delimiter/import gate.  None is
compiler-verified.

C2 now prepares the next exact layer.  It constructs periodic Fourier
negation as a self-equivalence, reindexes the C1b sum first by that
equivalence and then by `cmp99FinBoxZModEquiv`, and specializes the literal
physical Unit-E theorem to residue zero.  Its generated `a` is internal;
`rho`, the amplitude budget, the noncentral radius condition and the central
window remain visible because they are the actual analytic inputs produced by
the mass-uniform contour chain.  C2 has four public declarations and four
matching audit prints and passes the lightweight text gate, but is not
compiler-verified.

Static dependency inspection also exposes that Unit E is not one isolated
file: `BalabanCMP99PhysicalGreenFiniteGridAliasing` has a seventeen-pair
untracked analytic prefix (122 audit prints) from the centered torus,
holomorphy, contour telescope, mass-uniform Green bound, measure dictionary
and Fourier summability layers.  Its exact topological promotion order is
recorded in `STEP8B24-PROMOTION-MANIFEST.md`.  Therefore C2 cannot be promoted
immediately after C1b unless that prefix has first been validated and moved;
the generic Step 8b.22 cold seal is necessary but not sufficient.

After C2, steps 2--5 remain open: convert its scalar zero-residue identity to
the C1b Lie-fibre column without changing normalization, apply Unit F at the
same fine/coarse sizes, transport the owner metric, and only then package
regional `B0`.

C3 now prepares that scalar-to-fibre conversion explicitly.  It rewrites the
C1b point-source endpoint, factors the fixed Lie vector out of the finite sum,
and consumes C2.  Its conclusion is the generated `G Q'^*` point-source
column equal to the literal zero-residue physical Green series acting on the
same vector.  This closes the algebraic content of post-S4 step 2 at scratch
level.  The C3 source/audit pair has one public declaration, one matching
print and passes the exact-path text gate; it remains uncompiled.

After C3, steps 3--5 remain open: apply Unit F at
`Kfine = L^(depth+1)` and `N = 2*(K*Q)`, transport the owner metric through
`cmp99Eq389SourceLocalizationSiteEquiv`, and only then package the physical
regional `B0`.

Static inspection of Unit F exposes four additional untracked pairs beyond
the overlapping Unit-E analytic prefix: centered periodic residue summation,
the endpoint carry dictionary, the physical zero-residue bound and the
diagonal finite owner bound.  Together Unit E and Unit F have twenty-one
unique source/audit pairs and 171 audit prints.  This joint prefix is now
enumerated in the promotion manifest rather than hidden behind the phrase
“apply Unit F”.

C4a prepares the exact endpoint dictionary required by that application.
The C3 displacement `x-M*y` and Unit F's shortest periodic displacement can
have opposite signs at an even antipodal seam, so C4a deliberately does not
identify them as vectors.  It proves their centered `l1` lengths equal via
their common `ZMod` residue, then transports the signed-lattice exponential
weight to `finBoxDist (blockSite Kfine N x) y`.  C4a has four declarations,
four audit prints and a green exact-path text gate; it is not compiled.

After C4a, step 3 is reduced to combining the zero-residue scalar norm bound
with C3 and `norm_smul`.  Steps 4--5 — the source-localization owner transport
and physical regional `B0` package — remain open.

C4b prepares exactly that combination.  Its scalar theorem applies the
zero-residue bound to the literal negative fine-to-coarse displacement and
uses C4a to retain the fine-block owner decay.  Its vector theorem rewrites
the generated point-source endpoint by C3 and applies `norm_smul`; no
operator-norm readout or supplied endpoint equality is introduced.  The two
declarations and two audit prints pass the exact-path text gate, but remain
uncompiled.

Thus post-S4 step 3 is now closed at scratch/design level.  C5 transports
`blockSite (L^(depth+1)) (2*(K*Q)) x` through the sealed source-localization
site equivalence.

C5 is now prepared in scratch.  It evaluates C4b at the literal
`cmp99Eq389SourceLocalizationSiteEquiv L K Q depth target` and rewrites the
resulting fine-block owner to `cmp99Eq389SourceLocalizationOwner`.  Its one
declaration and one audit print pass the exact-path text gate, but remain
uncompiled.

Static signature audit rejects the earlier description of one final C6 that
would immediately package a *regional* `B0`.  C5 proves a point-source column
bound for the ambient complex operator

```text
generated flat complex Green ∘ literal Q'^*
```

with coarse source `y : FinBox 4 (2*(K*Q))`.  In contrast,
`CMP99Eq342SourceLocalizedGreenCertificate` requires four
`FinitePiLpTypedBlockLocalizedSupBound` fields for the canonical real
regional Dirichlet Green, its left derivative, right adjoint derivative and
Laplacian.  The quantified input there is an arbitrary field supported in a
source-owner fibre.  Neither the operator, scalar field, input carrier nor
quantifier agrees definitionally with C5.

The honest remaining chain is therefore:

* C6a names and proves nonnegativity of the depth-independent ambient
  point-source coefficient already explicit in C5;
* C6b upgrades the coarse point-source column theorem to the exact localized
  field contract, using the fact that the coarse source-owner map is the
  identity rather than paying a fibre-cardinality factor;
* C6c supplies the non-definitional ambient-complex-to-regional-real operator
  dictionary and the other three (3.42) actions, or records them as separate
  physical producers if they are not consequences of the value estimate.

Only after C6c may the coefficient be called the complete physical regional
`B0`.  Calling C5 or C6a that would rename the missing regional and derivative
obligations.

C6a is now prepared in scratch.  Its definition is exactly the product

```text
stabilized Green amplitude * residue-sum factor * exp(2*rho),
```

with the generated coefficient `a` fixed internally.  It proves
nonnegativity from the same strip inputs and rewrites C5 with no absorbed
factor.  Its definition plus two theorems have three matching audit prints and
pass the exact-path text gate.

C6b is also prepared in scratch.  It uses the identity owner on the coarse
carrier to prove that a field supported in one owner fibre is exactly one
`cmp99FlatComplexFibrePointSource`.  C6a then yields the owner-decaying bound
with `finitePiLpSupNorm`; no owner-fibre cardinality is paid.  Its two
theorems and two matching audit prints pass the exact-path text gate.  The
operator remains the ambient complex `G Q'^*`, so C6c remains unwritten and
load-bearing.  This audit is static only; no new declaration has been checked
by Lean.

The exact C6c type mismatch and its five-step accepted producer chain are
recorded in `STEP8B24-C6C-REGIONAL-FRONTIER.md`.  In particular, C6c is not a
single adapter: the `Q'^*`-restricted value action, the full regional Green
and the other three (3.42) actions are distinct obligations.

## Acceptance gates

1. **No diagonal cast.**  No proof may start from `K=L` and transport by
   equality of total cardinalities.
2. **Exact factorization visible.**  Every public endpoint states
   `L^(depth+1)` and `2*(K*Q)` (or the definitionally named equivalents).
3. **Generated inverse internal.**  No Green, inverse law, precision equality
   or family of Fourier solutions is supplied by the caller.
4. **Same generated scalar data.**  Spacing and `a` are the canonical values
   generated from `L`; no new free scalar is introduced.
5. **Orientation unchanged.**  The transpose/positive-phase convention of
   the sealed Gate-7 endpoint is preserved explicitly.
6. **No premature owner bridge.**  The diagonal item-4 theorem cannot feed
   `cmp99Eq389SourceLocalizationOwner` until S1--S4 are complete.
7. **No terminal overclaim.**  S1--S4 close post-Gate7 item 5 only.  Regional
   compression, physical `B0`, `norm R' < 1`, window 15 and terminal fields
   remain separate.

## Consequence for the roadmap

The prior fork is resolved as follows:

* not an arithmetic re-label of the diagonal endpoint;
* not a new two-scale generated tower;
* a finite source-separated Step-7b realization over the already generic
  tower and Fourier algebra.

This keeps item 5 substantial but bounded.  It should be implemented only
after the current Step 8b.22 cold verdict is sealed, and in small focal/audit
bricks following S1--S4.
