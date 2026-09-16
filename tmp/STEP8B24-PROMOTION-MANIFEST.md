# Step 8b.24 source-scale separation — promotion manifest

Status: static scratch only; no source below is compiler-verified.

Promotion is forbidden until the Step 8b.22 cold run has a terminal verdict
and its evidence has been sealed or its first real error diagnosed.

## Ordered bricks

### Brick S1a — real ambient inverse pair

1. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreen.lean`
2. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenAudit.lean`

Expected audit declarations: 5.

### Brick S1b — canonical complex inverse pair

3. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexification.lean`
4. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexificationAudit.lean`

Expected audit declarations: 4.

### Brick S2a — exact separated Step-7b carrier

5. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier.lean`
6. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrierAudit.lean`

Expected audit declarations: 6.

### Brick S2b — physical precision dictionary

7. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionary.lean`
8. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionaryAudit.lean`

Expected audit declarations: 2 public declarations.  The three supporting
lemmas remain private.

### Brick S3a — neutral noncentral fine-symbol substrate

9. `BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral.lean`
10. `BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentralAudit.lean`

Expected audit declarations: 1.  Move the generic theorem out of the
diagonal identification module in the same tracked change, and make the
diagonal module import the neutral substrate.  There must be one theorem,
not two duplicate declarations.

### Brick S3b — Green identification by inverse uniqueness

11. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentification.lean`
12. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentificationAudit.lean`

Expected audit declarations: 4.

The source-separated endpoint imports the neutral substrate and must not
consume the diagonal endpoint.

### Brick S4 — one-mode and finite-synthesis endpoint

13. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpoint.lean`
14. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpointAudit.lean`

Expected audit declarations: 4.

### Brick C0 — fixed-target endpoint-integrand normalization

15. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrand.lean`
16. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrandAudit.lean`

Expected audit declarations: 1.

C0 is downstream of S4 and the already sealed complete-fibre orientation
bridge.  It keeps one `ell`, `x` and `y` fixed and identifies the normalized
S4 mode with the literal CMP89 endpoint integrand.  It does not perform the
finite coarse-mode sum or attain an owner bound.

### Brick C1a — exact coarse point-source Fourier reconstruction

17. `BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction.lean`
18. `BalabanCMP99FlatComplexFibrePointSourceFourierReconstructionAudit.lean`

Expected audit declarations: 4.

This neutral brick proves FinBox character orthogonality, the exact
normalized point-source expansion, and its transport through an arbitrary
complex continuous-linear map.

### Brick C1b — generated point-source endpoint sum

19. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpoint.lean`
20. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpointAudit.lean`

Expected audit declarations: 1.

C1b composes C1a and C0.  Its conclusion is one normalized finite sum of the
literal CMP89 endpoint integrand for fixed physical target/source data.  The
Fourier-negation reindex and residue-zero aliasing still remain open.

### Required Unit-E physical prefix — pre-existing Step 8b.23 scratch

C2 cannot import `BalabanCMP99PhysicalGreenFiniteGridAliasing` directly from
the tracked tree: that module and its analytic prefix are still scratch.  The
exact topological order discovered from their active imports is:

1. `BalabanCMP89CenteredUnitCubeTorusQuotient`
2. `BalabanCMP89CenteredTorusFourierPhase`
3. `BalabanCMP99CenteredTorusSampleDictionary`
4. `BalabanCMP89Eq248GreenMassUniformHolomorphy`
5. `BalabanCMP89Eq248CenteredGreenTorus`
6. `BalabanCMP89Eq248DisplayedGreenVectorPeriodicity`
7. `BalabanCMP99CenteredTorusPhysicalGreenSampleTransport`
8. `BalabanCMP89SignedLatticeL1TotalSum`
9. `BalabanCMP89Eq248GreenOneCoordinateContourShift`
10. `BalabanCMP89Eq248GreenProductContourTelescope`
11. `BalabanCMP89Eq248MassUniformGreenBound`
12. `BalabanCMP89Eq248MassUniformNormalizedGreenBound`
13. `BalabanCMP89NormalizedBrillouinToTorusMeasure`
14. `BalabanCMP89CenteredTorusGreenCoefficientPhase`
15. `BalabanCMP89CenteredTorusGreenCoefficientDictionary`
16. `BalabanCMP89CenteredGreenFourierSummability`
17. `BalabanCMP99PhysicalGreenFiniteGridAliasing`

Every item has one source draft and one sibling audit draft.  The audits
contain `122` `#print axioms` commands in total.  This is a promotion prefix,
not evidence that any item is compiler-verified.  It must be validated in
ordered, restartable bricks after the generic Step 8b.22 seal; a broad green
on the last file without per-brick evidence is not accepted.

### Brick C2 — Fourier-negation reindex and zero-residue aliasing

55. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalZeroResidueAliasing.lean`
56. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalZeroResidueAliasingAudit.lean`

Expected audit declarations: 4.

C2 constructs Fourier negation as an involutive `FinBox` equivalence,
reindexes the finite endpoint sum through `FinBox ≃ ZMod`, and specializes
the physical Unit-E theorem to residue zero.  The generated coefficient is
internal; only the literal common-radius amplitude/radius/window conditions
survive.  C2 requires green C1b and the complete Unit-E prefix above.

### Brick C3 — generated point-source zero-residue endpoint

57. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceZeroResidue.lean`
58. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceZeroResidueAudit.lean`

Expected audit declarations: 1.

C3 composes C1b and C2 and transports their scalar equality through the
fixed Lie-coordinate vector.  Its conclusion is the literal generated
`G Q'^*` point-source column equal to the physical zero-residue coefficient
series at the same endpoint displacement.  It closes the exact readout
identification in post-S4 step 2, not the Unit-F owner estimate.

### Required Unit-F extension — four further Step 8b.23 pairs

The Unit-E prefix and Unit-F prefix overlap in thirteen analytic pairs.  Unit
F adds exactly four source/audit pairs after that common prefix:

1. `BalabanCMP89CenteredPeriodicL1ResidueSum`
2. `BalabanCMP99CenteredPeriodicEndpointDictionary`
3. `BalabanCMP99PhysicalGreenZeroResidueBound`
4. `BalabanCMP99DiagonalFiniteGreenOwnerBound`

Their audits contain `49` prints.  Thus the joint Unit-E/Unit-F prefix has
twenty-one source/audit pairs and `171` audit prints, not two independent
seventeen-pair trees.

### Brick C4a — literal endpoint to Unit-F owner dictionary

67. `BalabanCMP99SourceFineToCoarseCenteredOwnerDictionary.lean`
68. `BalabanCMP99SourceFineToCoarseCenteredOwnerDictionaryAudit.lean`

Expected audit declarations: 4.

C4a proves equality of centered `l1` lengths, not equality of signed
representatives, between the literal `x-M*y` endpoint and Unit F's shortest
periodic displacement.  It then transports the diagonal weight bound to the
actual coarse source `y`.  This is the antipodal-seam-safe dictionary required
before the generated point-source estimate can consume Unit F.

### Brick C4b — Unit-F generated point-source owner bound

69. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBound.lean`
70. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBoundAudit.lean`

Expected audit declarations: 2.

C4b combines the literal zero-residue scalar bound, C4a and C3.  It retains
the physical amplitude, residue factor, boundary factor, fine block owner and
the norm of the actual Lie-coordinate source.  This closes post-S4 step 3 at
scratch level; source-localization owner transport and regional `B0` remain.

### Brick C5 — source-localization owner transport

71. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalSourceOwnerBound.lean`
72. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalSourceOwnerBoundAudit.lean`

Expected audit declarations: 1.

C5 evaluates the C4b point-source estimate at the sealed
`cmp99Eq389SourceLocalizationSiteEquiv` and rewrites its fine-block owner to
the literal `cmp99Eq389SourceLocalizationOwner`.  It closes post-S4 step 4 at
scratch level.  It does not yet produce the physical regional `B0`: the
remaining C6 work is split into the ambient coefficient, the localized-field
quantifier, and the non-definitional regional/derivative dictionaries.

### Brick C6a — named ambient point-source coefficient

73. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceB0.lean`
74. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceB0Audit.lean`

Expected audit declarations: 3.

C6a names the exact coefficient already displayed by C5, derives its
nonnegativity from the same physical strip inputs, and states the C5 estimate
in that normal form.  Its public name deliberately contains `PointSourceB0`:
it is not the regional four-action (3.42) package.  C6b/C6c remain open.

### Brick C6b — identity-owner localized coarse field

75. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0.lean`
76. `BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0Audit.lean`

Expected audit declarations: 2.

C6b proves that a coarse field supported in an identity-owner fibre is the
literal point source at that owner, then upgrades C6a to the existing finite
supremum norm.  It introduces no fibre-cardinality factor.  The operator is
still ambient, complex and composed with `Q'^*`; C6c remains open.

### C6c — regional four-action frontier (design only)

The exact tracked-tree inventory is recorded in
`STEP8B24-C6C-REGIONAL-FRONTIER.md`. At current HEAD the normalized Fourier
Green value and its left forward difference exist, but there is no tracked
producer for the regional actions `G' D*` or `Delta G'`. Direct visual
inspection of CMP89 Lemma 2.4 and CMP96 Proposition 2.2 fixes why: Fourier
analysis supplies `G_j Q_j^*`, its left derivative/Hölder difference and the
coarse covariance; the CMP96 local parametrix/random-walk construction later
produces the complete action list (2.67), including `G' D*` and `Delta G'`.
They must not be invented as independent Fourier endpoints. The sealed
physical weighted-adjoint work only fixes the orientation of `Q'^*`.
Likewise, `BalabanCMP99SourceRegionalGreenNeumann` assembles local Dirichlet
Greens into the ambient inverse and cannot be used in reverse to deduce local
bounds from C6b.

The weighted-row *algebra* is not missing: the tracked
`FinitePiLpTypedWeightedRowKernelBound` composition theorem supplies
same-rate submultiplicativity, and the Eq.-(3.95) modules demonstrate its
power/Neumann use.  Only that generic layer is reusable.  The Eq.-(3.95)
physical correction inverts the coarse covariance rather than the fine
regional Green, while the later Eq.-(3.89) owner-row theorem already consumes
`CMP99Eq342SourceLocalizedGreenCertificate`.  Neither is a producer of the
certificate.  CMP96 (2.48)--(2.66) additionally requires its printed
multiscale distance, separation window (2.59), and volume-free convolution
bound before applying the generic algebra to the correct defect.

Accordingly no C6c source module is prepared yet. Its admissible route is the
primary-source chain CMP89 Lemma 2.4 -> CMP89 (2.34) -> CMP95 -> CMP96
(2.40)/(2.43)/(2.60)--(2.67) -> CMP99 Corollary 3.6, ending at the literal four-field
`CMP99Eq342SourceLocalizedGreenCertificate`.  A record that accepts those
four bounds would only rename (3.42) and is forbidden.

The zero-mass left-derivative subroute is now separately bounded in
`STEP8B24-C6C1-DERIVATIVE-DESIGN.md`: it must inherit mass-uniform
holomorphy and the seam from the two literal Green endpoints through the
tracked forward-difference identity, before taking norms.  Four restartable
bricks D1--D4 are named there; none is yet prepared or compiler-verified.

## Promotion gates

For each brick:

1. Copy the corresponding `.draft.lean` bytes deliberately and replace only
   the commented promotion imports with real tracked imports.
2. Add the unequivocal PRE-VALIDATION module docstring required by current
   governance, after imports.
3. Run the overlay guards on exactly the promoted paths.
4. Compile focal source and audit in Colab or a prepared diagnostic workflow;
   never on Windows.
5. Stop on first real error.  Do not continue to later bricks.
6. A cached pass is diagnostic only.  A cold checkout is required before
   removing PRE-VALIDATION or citing the brick as sealed.
7. Audit output must contain exactly the allowed axiom set for every printed
   declaration, with no `sorryAx` or parser-derived false PASS.

## Semantic gates

* Public types retain `L`, `K`, `Q` independently.
* Fine Fourier block side is `L^(depth+1)`.
* Coarse Fourier side is `2*(K*Q)`.
* Ambient owner factorization is
  `(K*L^(depth+1))*(2*Q)` through the named source-separated equivalence.
* No `K=L` hypothesis or diagonal endpoint appears.
* Green and inverse laws are constructed internally.
* Generated spacing and `a` depend on `L`, not `K`.
* Positive phase and transposed coefficient orientation stay explicit.
* S4 closes scale separation only; it does not claim regional `B0`, window 15
  or a terminal field.
* C5 is only an ambient complex `G Q'^*` point-source column estimate.  It may
  not be used as a `CMP99Eq342SourceLocalizedGreenCertificate` without the
  localized-field and regional real-operator bridges named in the design.

## Static scratch gate (2026-08-17)

This gate is textual/static only.  It is not Lean evidence and does not alter
the PRE-VALIDATION status.

* Seven S1--S4 source drafts and seven sibling audit drafts checked.
* S1--S4 public declarations: `26`.
* Matching S1--S4 `#print axioms` commands: `26`.
* Missing audit declarations: `0`; extra public declarations: `0`.
* Forbidden proof placeholders (`sorry`, `admit`, `by?`, `exact?`): `0` after
  stripping comments and strings.
* Delimiter imbalances in `()`, `[]`, `{}` and `⟨⟩`: `0` after stripping
  comments and strings.
* Ordered import graph: `11` tracked imports and `6` imports of prior drafts;
  no missing or forward imports.
* Diagonal-endpoint code/import dependencies and `K = L` code hypotheses: `0`.

Result: `STATIC_GATE_STEP8B24=PASS`.  Compilation remains forbidden until the
Step 8b.22 cold run has a terminal verdict and that verdict is handled.

The later C0/C1 source/audit pairs were checked separately: six public
declarations, six matching prints, no placeholders, balanced delimiters and
all tracked/prior-draft imports resolved.
`STATIC_GATE_STEP8B24_POST_S4=PASS`; this is likewise not elaboration evidence.

C2 adds four public declarations and four matching prints.  Its exact two
files pass `scripts/check_lean_overlay_text.py`; its two promotion imports are
the tracked weighted-adjoint substrate and the still-scratch Unit-E physical
endpoint.  `STATIC_GATE_STEP8B24_C2=PASS` is textual evidence only.

C3 adds one public declaration and one matching print; its exact source/audit
pair also passes the overlay text guard.  `STATIC_GATE_STEP8B24_C3=PASS` is
textual evidence only.

C4a adds four public declarations and four matching prints; its exact pair
passes the overlay text guard.  `STATIC_GATE_STEP8B24_C4A=PASS` is textual
evidence only.

C4b adds two public declarations and two matching prints; its exact pair
passes the overlay text guard.  `STATIC_GATE_STEP8B24_C4B=PASS` is textual
evidence only.

C5 adds one public declaration and one matching print; its exact pair passes
the overlay text guard.  `STATIC_GATE_STEP8B24_C5=PASS` is textual evidence
only.

C6a adds one definition, two theorems and three matching prints; its exact
pair passes the overlay text guard.  `STATIC_GATE_STEP8B24_C6A=PASS` is
textual evidence only.

C6b adds two theorems and two matching prints; its exact pair passes the
overlay text guard.  `STATIC_GATE_STEP8B24_C6B=PASS` is textual evidence only.

## Static semantic signature audit (2026-08-17)

The seven source signatures were read in full after the mechanical gate.

* S1 fixes the flat background, zero closed budget, spacing and generated
  coefficient internally.  Its only scalar regime input is the pre-existing
  physical assumption `hL : 2 ≤ L`; both ordered inverse laws are proved.
* S2a constructs the active-site, ambient-site and field equivalences.  S2b
  proves the pointwise real dictionary first and promotes it to the complex
  operator equality by real/imaginary decomposition.  No carrier or precision
  equality is accepted from the caller.
* S3 constructs the transported Green, derives its inverse law from S1/S2,
  proves the central denominator nonzero from the generated positive
  coefficient, and consumes the neutral noncentral theorem.  The local `hk`
  argument only selects a noncentral alias; it is not a physical obligation.
* S4 is a consequence-only layer: one-mode action, selected-fibre DFT,
  off-fibre zero and finite synthesis.  It accepts no inverse, summability,
  regional-decay or terminal-field hypothesis.
* Across all public source signatures the only named proof input is `hL`, plus
  the local off-central/off-fibre index exclusions.  There is no caller-supplied
  Green family, inverse law, precision identity, nonvanishing family, `K = L`
  cast or physical endpoint equality.

This is a static contract audit, not elaboration evidence.

## Exact promotion footprint

Promotion of S1--S4 creates the fourteen ordered source/audit modules above
and also
modifies the existing diagonal module
`BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentification.lean`: the neutral
noncentral theorem is removed from that file and replaced by an import of the
new neutral substrate.  Its existing audit remains valid and must continue to
print the same theorem from the new owner module.  The theorem must have one
definition site globally.

The extracted theorem body was compared byte-for-byte after LF
normalization against its current tracked definition: `68` lines on each
side, exact equality, normalized SHA-256
`4299893451956cd1e3749224c621b539b54657413784918fb7f80f92a81e6a70`.
Thus promotion is an ownership move, not a proof rewrite.

The stronger read-only gate `tmp/audit_step8b24_ownership_move.py` also
simulates the edit to the existing owner: add the neutral-module import,
remove only the old declaration, preserve every unrelated declaration in
order, retain the old audit readout, require the new sibling audit, and reject
any dependency on the diagonal owner from the source-separated consumer.  It
reports

```text
STEP8B24_OWNERSHIP_MOVE_STATIC_OK theorem=cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral block_lines=71 block_sha256=119FE96DF43A1574FAE315A3ADEDDA6C5ABF26038D6570627A8387E0B2E9EC34 proposed_old_owner_sha256=4793DC4EEFBB874A2E696099C3DB614A78C4EE86297D352E5049BF517FC0F7C3 old_audit=retained neutral_audit=present separated_consumer=explicit
```

The 71-line block includes the three-line declaration doc comment; the
theorem declaration/proof itself is the previously recorded 68 lines.  The
ownership-audit script SHA-256 is
`BC29674AE6B4201801B43DB95C7DC17C19EE694477417FEED3FB8245814F1A35`.
This remains a static proposed-delta audit, not a compiler seal.

The seven S1--S4 audit modules must be added to `YangMillsCore.lean` only when
their corresponding sources are promoted.  Thus a complete root-sealed
promotion touches fifteen RG source/audit paths plus the root aggregator; it
is not merely a byte copy of the fourteen scratch files.

Promoting C0 later adds two more RG paths and one further root-audit import.
It must follow a green S4 and is not part of the `26/26` S1--S4 count.
Promoting C1a/C1b adds four further RG paths and two root-audit imports; C1b
must follow green C1a and C0.  The prepared Step-8b.24 dependency footprint is
therefore twenty new modules before the Unit-E prefix.  The shared
Unit-E/Unit-F dependency prefix adds forty-two modules and twenty-one
root-audit imports; C2, C3, C4a, C4b, C5, C6a and C6b add fourteen modules
and seven root-audit imports.  That dependency closure contains seventy-six
new modules, one existing diagonal source ownership edit, and thirty-eight
new root-audit imports.

The full scheduled Step-8b.23 promotion has one additional independent Unit-A
pair, `BalabanCMP89CenteredBrillouinAffineSlice` plus its audit, which the
Step-8b.24 consumers do not import.  It was previously omitted from the
Step-8b.23 exact path list even though its manifest retained it.  Counting the
whole scheduled promotion rather than only the Step-8b.24 dependency closure
therefore gives **seventy-eight** new modules, one existing diagonal source
ownership edit, and **thirty-nine** new root-audit imports.  They must be
promoted as ordered, restartable bricks rather than as one unvalidated batch.

The read-only whole-schedule gate `tmp/audit_step8b24_promotion.py` now checks
that footprint directly.  On 2026-08-17 it reported

```text
STEP8B24_PROMOTION_STATIC_OK files=78 sources=39 audits=39 declarations=222 prints=222 dependency_edges=48 source_promotion_imports=23 ownership_moves=1 content_manifest_sha256=F7600849BBC58362F419446F2C114C133112BC1EEF5581D56F63AE3F6D73EE32
```

It additionally checks exact sibling-audit coverage, proposed tracked target
collisions, public declaration collisions, resolution and acyclicity of every
active or explicitly commented promotion import, and the single deliberate
ownership move of
`cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral` out of
the existing diagonal module.  It also derives the complete schedule and
requires byte-for-byte path-list agreement with `tmp/STEP8B24-ALL-PATHS.txt`.
The exact list SHA-256 is
`04D159C779790BBC9E7B5CB6BEB98EE1309245B252AD177E7D97C359819EE63B`;
the 78-file overlay text gate reports `LEAN_OVERLAY_TEXT_OK`.  The audit-script
SHA-256 for this checkpoint is
`4D76AB806AF59DE6242EDA4F34B8272DC416F1CF04EF77F5CC9D387C0C7B0E63`.
This remains static evidence only: none of the 78 modules is compiler-verified
by this gate.

The earlier `dependency_edges=29` report counted only imports already active
inside scratch files and was incomplete.  The corrected gate includes the 23
source promotion imports that are deliberately commented until the modules
exist; after deduplication the actual internal graph has 48 edges.  No prior
compiler claim depended on the undercount.

The deterministic whole-schedule preview
`tmp/audit_step8b24_promotion_preview.py` now applies the corresponding
comment-only/import transformations in memory.  It activates all 58 commented
promotion imports (23 source dependencies and 35 sibling-audit imports),
preserves and normalizes the 17 existing module docstrings, inserts the
mandated PRE-VALIDATION docstring in the other 61 files after their final
import, and compares comment-stripped visible commands before and after.  It
reports

```text
STEP8B24_PROMOTION_PREVIEW_OK files=78 declarations=222 imports_activated=58 docstrings_existing=17 docstrings_inserted=61 status_comment_changes=89 import_prefix_ok=78 promoted_content_manifest_sha256=5257708D43BD0C60FF5DA388C4E73E50F2D9307FFF7D1BFF4E4A929D732F6A97
```

The preview-script SHA-256 is
`36293E060BECE2A7E5EDF183BAC8D5E4443083A07C3AB577624768AD0627FBE2`.
The first preview attempt failed only because its comparator retained blank
comment lines; the corrected comparison drops empty visible lines and changes
no draft.  This digest covers the 78 new blobs only; the separately audited
existing-owner edit remains the 79th tracked delta.

**Staged-promotion correction (2026-08-17).**  The 78-file digest above is a
valid simultaneous whole-graph static measurement, but it is not the later
promotion contract.  Step 8b.23 is deliberately sealed first, so by the time
Step 8b.24 is promoted its 44 A--F source/audit prerequisites already exist
and have had their PRE-VALIDATION marks removed.  Moreover, the Step-8b.23
and aggregate Step-8b.24 transforms differ bytewise on all 44 shared drafts.
Reusing the aggregate preview after staged sealing would therefore either
fail on existing targets or rewrite already certified modules.

The authoritative staged boundary is now
`tmp/audit_step8b24_extension_promotion_preview.py`.  It computes the exact
sealed bytes expected for the 44 immutable A--F prerequisites, rejects a
partial prerequisite state or any byte drift, creates only the 34 S1--C6b
source/audit targets (17 bricks, 49 declarations), and includes the one
existing-owner edit in the same 35-row content manifest.  In the present
pre-Step-8b.23 tree it reports the intentionally future state

```text
STEP8B24_EXTENSION_PROMOTION_PREVIEW_OK state=future
  prerequisites_present=0 prerequisites_absent=44
  new_files=34 modified_files=1 modules=17 declarations=49
  imports_activated=40
  prerequisite_manifest_sha256=242097332A9545564915A67424A7E34984D477B5B6FA2E918619C27BFC463457
  extension_manifest_sha256=CD6723D3B6EC70B9C004998BB25721E98A474F303F45AB09465DE6E3EE714C6B
```

The extension-preview script SHA-256 is
`3CC75BE247888B1787E77EB61CAF7B4B57FEAFDACE090FAC32E6D96368D7EA84`.
The aggregate preview remains historical whole-schedule design evidence and
is superseded only as an executable staged promotion contract.

Semantic-audit refresh (2026-08-17): C6a's prose incorrectly described its
named coefficient as depth-independent even though the definition contains
`depth` through the generated physical `a`, and no uniform-in-depth theorem
is present.  Only that scratch documentation was corrected; declarations and
proofs are unchanged.  The two content digests above are the resulting
refreshed values.  `tmp/STEP8B24-C4-C6B-SEMANTIC-AUDIT.md` records the open
uniform-depth, regional-real-Green and derivative-action obligations.

The complete S1--C6b semantic reports are:

```text
STEP8B24-S1-S4-SEMANTIC-AUDIT.md    400E48A2C55E0166C16015EF9B1E285817AFBA5C657F34FA5297A1B32D66AC8E
STEP8B24-C0-C3-SEMANTIC-AUDIT.md    FAEEBE54AD21A89C73943EB8A6E80691BEF07BEED00D459B22C098C92CC89C40
STEP8B24-C4-C6B-SEMANTIC-AUDIT.md   BBA50CF38C889DBECD8DC6DE53763998286E0B80F72E170F32D2248759B21A82
```

They are design evidence only, not elaboration or axiom evidence.

The complete restartable queue is fixed by
`tmp/audit_step8b24_brick_schedule.py`: all 22 Step-8b.23 units precede the
17 S1--C6b consumers, every active/commented dependency points backward, and
the neutral-theorem ownership edit is attached to brick 27 rather than left
as a floating change.  It reports

```text
STEP8B24_BRICK_SCHEDULE_OK bricks=39 declarations=222 dependencies=48 source_promotion_imports=23 ownership_move_at=27 schedule_sha256=43BC9CBEFEF9423CCBD6D181BD1E47187440EE129B1A2B2DD132E1FCC67309
```

The schedule-script SHA-256 is
`8A85CA7CB0A8241E4830B4AF69E0A5E3DE2C3C8D54FF4172C0487A79716E8F4F`.
Its first run found that the C2 audit contained all four declarations but
printed the equivalence before its prerequisite involutivity theorem.  The
scratch audit was reordered to match source order (no theorem or proof
changed), SHA-256
`C066F63B3F8A6775DD25AE3156D3B7D06DC4590C37A39E5A8BA9213B21E66C58`;
all 78-file gates were then rerun and passed with the refreshed digests above.

Root aggregation is likewise fixed rather than left to manual insertion.
`tmp/audit_step8b24_root_import_preview.py` appends exactly the sibling audit
for each of the 39 bricks in schedule order, checks every intermediate prefix
with the late-import rule, and rejects duplicates against the existing root.
At the present tracked base it reports

```text
STEP8B24_ROOT_IMPORT_PREVIEW_OK base_imports=1548 additions=39 final_imports=1587 base_sha256=D67B9303985DEBB39A2ED1CF9990D450A380A3F5A6AF6EFFBD875C765F18B0F1 final_sha256=38DE30EB48B4DF0263284922CAEAE132A497B0D6B3BFD765357DE92C9114A60E prefix_chain_sha256=D7CADEACC0D9E6D7C91CEA81E2F8C709B3FAD8F4E1E230A2435D51C5C76AE3F7
```

The script SHA-256 is
`1882433309802D0CA4DD1EEA3AFEA2E35C79F3B61ADCCF57867705B0411B57DD`.
Any intervening tracked root edit invalidates the base hash and requires this
preview to be regenerated before promotion; it is not a compiler claim.

For the same staged reason, the executable root contract is now
`tmp/audit_step8b24_extension_root_import_preview.py`: it requires either
none or all 22 Step-8b.23 audit imports, rejects partial state and existing
S1--C6b imports, and appends only the 17 extension audits.  Its current future
simulation reaches the same final root hash as the whole-schedule preview:

```text
STEP8B24_EXTENSION_ROOT_IMPORT_PREVIEW_OK state=future
  current_imports=1548 prerequisites_present=0 prerequisites_simulated=22
  extension_additions=17 final_imports=1587
  prerequisite_base_sha256=A89D80825BFB64DE83240D2BC2D06136E28553B47ABE687604574FE095731DBD
  final_sha256=38DE30EB48B4DF0263284922CAEAE132A497B0D6B3BFD765357DE92C9114A60E
  prefix_chain_sha256=EF043230C7FF0D3986255DEAA4544A26A68E39EA9C991F68825BD1DC67A58519
```

Its SHA-256 is
`E3219758DDF1A04628A47BDB66F432B05E5EDB02727B6F9097FE4A724ABFDECF`.

Validation scope follows the same staged boundary.
`tmp/generate_step8b24_extension_validation_runner.py` hash-gates the 34 new
S1--C6b files plus the modified old owner and its unchanged audit.  After the
neutral theorem's own focal/audit, it recompiles that old pair and requires
all four historical readouts, including the moved theorem now resolved by
import.  Consequently the exact queue is 17 new bricks, 18 validated pairs,
36 child stages and 53 axiom blocks (49 new plus four old-owner readouts), not
the tempting but incomplete 34-stage queue.  The fail-closed synthetic check
reports

```text
STEP8B24_EXTENSION_RUNNER_SELFTEST_OK runner=pass workflow=pass
  new_bricks=17 validated_pairs=18 files=36 stages=36 axiom_blocks=53
  ownership_tamper=fail_closed
  generator_sha256=93EFF7CBA23FB4616BA365B3447BA01B68B461FAF7563FB61BDDF389144C0F7B
```

The test-script SHA-256 is
`6FFAA77184979C76F83ADED055D7BF1DF546F096ACA34BE91941062FDBED2BF7`.
The cold terminal companion
`tmp/generate_step8b24_extension_terminal_workflow.py` additionally fixes all
44 sealed Step-8b.23 prerequisite blobs and the 36 validation paths, for an
80-blob source gate.  It executes the 17 new pairs plus the old owner/audit
at the ownership boundary, independently rechecks the unique new theorem
owner and retained old-audit readout, compiles its embedded 53-block axiom
verifier and fails closed if a prerequisite regains PRE-VALIDATION.  Its
SHA-256 is
`7DD2029B1C9664BFAAC36B706D7FC029075305E31CF8F8B6BBA83F5B24268055`.

Cold-artifact acceptance is prepared independently in
`tmp/audit_step8b24_extension_cold_evidence.py`.  It reconstructs the exact
80-blob manifest from Git objects and checks source/workflow SHAs, cold mode,
toolchain and Mathlib pins, all 36 child exits, 18 literal build sentinels,
53 allowed axiom blocks, the recorded axiom JSON, terminal status, every
content checksum, deterministic inner archive and raw outer ZIP.  Its
synthetic positive/tamper test reports

```text
STEP8B24_EXTENSION_COLD_EVIDENCE_SELFTEST_OK positive=pass
  tamper=fail_closed files=80 stages=36 axiom_blocks=53
```

The validator SHA-256 is
`6EE0E19F2D00E0B0979B77C509814423FC383908E97021390F7CF20806D318FD`;
the test SHA-256 is
`D773F25680BDFC924136FBFF17313456CDF33707448B0201F3518BE1E896EACD`.
These are instrumentation gates only; they cannot substitute for the later
cold artifact.

`tmp/retrieve_step8b24_extension_cold_evidence.ps1` is the corresponding
fail-closed retrieval path.  It requires the exact successful workflow SHA,
authenticated `lluiseriksson`, one exact artifact name and a fresh
destination; retains the raw binary ZIP separately from the extracted copy;
and invokes the independent validator above.  Parser-only validation reports

```text
STEP8B24_EXTENSION_RETRIEVER_PARSE_OK
  sha256=5B8DCDA50609A3EFE99467A7D262A686367C1968C3FEA8DACEF51A7E6DB21AB6
```

It must not be invoked before the later external terminal verdict.
This is runner preparation only; none of S1--C6b has been elaborated.

The mechanical writer `tmp/promote_step8b24_extension.py` is gated by the
same contract.  It requires an explicit exact HEAD and clean tracked state,
verifies all 44 sealed A--F targets byte-for-byte against prerequisite digest
`242097332A9545564915A67424A7E34984D477B5B6FA2E918619C27BFC463457`,
requires each of the 22 sealed A--F audit modules to be imported by
`YangMillsCore.lean`,
requires all 34 extension targets absent, and writes those targets together
with the old-owner edit only under `--write`.  The 35 post-write bytes must
match extension digest
`CD6723D3B6EC70B9C004998BB25721E98A474F303F45AB09465DE6E3EE714C6B`.
Current read-only checks report

```text
STEP8B24_EXTENSION_PROMOTION_PLAN_OK prerequisites=44 new_files=34
  modified_files=1
  manifest=CD6723D3B6EC70B9C004998BB25721E98A474F303F45AB09465DE6E3EE714C6B
STEP8B24_EXTENSION_PROMOTION_GATE_OK
  current_state=blocked_until_44_prerequisites_sealed
```

The writer SHA-256 is
`B436B830037F1EE8FEB6CF99C774747362B6EBB0257C842FEB2AAE6D96196CF9`.
Its current refusal is intentional; it cannot race either Step 8b.23 seal.

After adding the core-import prerequisite, the complete lightweight Step
8b.24 instrumentation regression (promotion/static/preview/schedule,
extension preview, both root previews, runner self-test, evidence self-test,
and ownership audit) reports

```text
STEP8B24_INSTRUMENTATION_REGRESSION_OK scripts=9
  elapsed_s=3.661 peak_rss_bytes=30965760
```

The writer itself fails closed on the current tree at the first absent A--F
prerequisite, before any write:

```text
SEALED_PREREQUISITE_MISSING=YangMills\RG\BalabanCMP89CenteredBrillouinAffineSlice.lean
```

## Counter discipline

Even a cold-green S1--S4 does not change `20/41`, does not inhabit
`TermSource`, and does not by itself attain window 15.  It closes the
post-Gate7 scale-separation item required before the physical owner bridge.
The exact post-S4 aliasing/readout/residue-zero/owner composition is listed in
`STEP8B24-SCALE-SEPARATION-DESIGN.md` and remains open; therefore S4 must not
be reported as a regional `B0` producer.

## Downstream C6c.2 boundary (static, 2026-08-17)

`STEP8B24-C6C2-EQ234-DESIGN.md` fixes both the exact printed one-step Green
recurrence (2.42) and the resulting CMP89 (2.34) finite RG-scale sum, and
audits the closest tracked objects.  The existing regional
coarse-covariance telescope changes `Omega` and cannot implement (2.34).
The retained stratum covariance uses the final Green at every stratum and
cannot implement the source prefix family `G_j` either.  The missing brick is
an internally generated family of prefix precisions
`-Delta_A + m^2 I + a_j (L^j eta)^(-2) Q_j(A)^dagger Q_j(A)`, their Greens on the
original fine carrier, the literal effective quadratic operator
`Delta^(j) = a_j (L^j eta)^(-2) I - a_j^2 (L^j eta)^(-4)
Q_j G_j Q_j^dagger` from CMP85 (2.21), and the literal coarse covariance
`C^(j) = (a (L^(j+1) eta)^(-2) P(A) + Delta^(j))^(-1)` from (2.30).
Only then may it prove the recurrence
`G_(j+1) = G_j + a_j^2 (L^j eta)^(-4) G_j Q_j^dagger C^(j) Q_j G_j`
and the finite induction from `G_1 = C^(0)`.  It is
downstream of C6c.1, has no promoted Lean source, and does not enlarge the
current promotion footprint.

The primary/source dictionary has three distinct scalars and the future
signatures must keep them distinct: bare physical mass `m`, flowing averaging
coefficient `a_j` (historically named `cmp99SourceMassParameter` in Lean),
and the separately normalized coefficient
`cmp99SourceGeneratedPhysicalMass`.  The generic CMP85 recurrence retains
`m`; the hRpoly specialization fixes `m := 0` internally.  This is measured
in the sealed theorem
`physicalPrecision_complexification_eq_fullComplexAction`, whose target is
the literal full-complex action at scalar mass zero and generated averaging
coefficient `A`.  Thus no bare mass is missing from the present hRpoly
physical operator, but omitting `m^2` from the generic source recurrence or
identifying it with either averaging coefficient is rejected.

The source/Lean coefficient offset is part of the acceptance contract:
source `a_1 = a` corresponds to
`cmp99SourceMassParameter a (Lblock : R) 0`, so source
summand `j` uses Lean coefficient index `j - 1`; this is not the same index as
the physical operator prefix `Q_j`/`G_j`.

For the physical package the printed RG factor is not a second free scale:
instantiate the tracked tower's internally named parameter as
`M := Lblock` and specialize `L` definitionally to `(Lblock : R)`.  This is
the same factor that proves
`terminalSpacing = (Lblock : R)^j * spacing`.  The later regional parameter
`K` remains independent; the rejected diagonal specialization `K=Lblock` is
not restored.  An independent real `L` and a caller equality hypothesis
would merely relocate the scale dictionary and is rejected.

`STEP8B24-C6C2-PREFIX-GREEN-BRICKS.md` now bounds this frontier as six
restartable stages, with P2 split into fine Green, effective precision and
literal coarse precision: canonical truncation/`towerAt` bridge, retained raw
prefix Poincare, source-`a_j` P2a/P2b/P2c, exact (2.41)--(2.42), finite
induction, and carrier/spacing transport.  The tracked inverse of
`Q_j G_j^2 Q_j^dagger` is a conditional-covariance object and is explicitly
not a producer of CMP85 (2.30).  P1 must use
the chain-generic tracked theorem
`CMP99SourceActiveRegionChain.norm_sq_le_absorbed_poincare` on the P0
truncation; the specialized `cmp99SourceIteratedLift_..._with_Qprime` theorem
has the wrong intermediate-prefix lattice in its public signature.  The
printed base `G_1=C^(0)` is now isolated as P4a: (2.17) defines
`Delta^(0)` separately, so the producer must construct the literal
(2.17)+(2.30) base precision, prove it identical to the P2a precision of
`G_1` using `a_1=a` and `Q_1=Q_step`, and then apply inverse uniqueness.
It may not instantiate the positive-level Schur/P2c package at zero, be
hidden inside the scale-sum induction, or be supplied by the caller.  The
scratch implementation now contains sixteen source modules and sixteen
complete sibling audits: P0, P1, P2a, P2b, P2c, the eight-file P3 chain,
P4a, P4b and P5, plus the separate aggregate P3 audit.  They expose 156
public declarations, pass the exact 33-file text/byte gates, and remain
wholly unelaborated.  Those thirty-three
paths are not part of either tracked promotion footprint above until their
own ordered diagnostic and cold seal exist.

An additional upstream scalar brick is now separated from those 32 paths:
`BalabanCMP99SourcePoincarePositiveRadiusReachability`.  Static inspection
showed that P0--P5 consume one terminal
`cmp99SourcePoincareErrorCoeff ... < 1`, while the existing joint-regime
witness does not produce it and the tree only closes it at `epsilon = 0`.
The new two-file scratch brick proves the proposed route by continuity at
zero, exposes an admissible interval `0 <= epsilon < radius`, intersects it
with the closed `Ubar` budget at the same radius, and derives a literal flat
background inhabitant, and restricts the existing CMP109 pivot witness to the
same positive radius by the two literal linear formulas.  It has seven
proposed declarations and seven audit
prints; source SHA-256 is
`5659CCC5C4FEA43794AE57E399B195961A9662A47B1E5F032471E14B17BC9FAC`
and audit SHA-256 is
`2EB33641451CFF2F25D0685E9634FCA2DECED191BFF8D06B02AAEF34B3C961B7`.
It is text-guarded but unelaborated, is not a sixteenth freely chosen window,
and moves no counter.

Its deterministic read-only promotion preview preserves all seven names,
places the PRE-VALIDATION docstring after the imports, activates the exact
sibling audit and yields promoted-content manifest SHA-256
`C020325705C5AB758EF91FBFEA4E4F3573EBD94C1F9B57F1DBD27F5E8107D508`.
No tracked target has been written.
