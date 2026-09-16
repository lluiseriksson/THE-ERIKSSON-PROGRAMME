# Step 8b.23 promotion manifest — static, not compiler evidence

This manifest fixes the finite promotion order from the mass-uniform Green
contour construction to the literal CMP99 finite-grid aliasing theorem.  All
listed Lean files currently live under `tmp/*.draft.lean`; none is a tracked
producer and none may remove `PRE-VALIDATION` until its own focal and axiom
audit have passed on the sanctioned remote compute plane.

The current Step 8b.22 cold run must receive its terminal verdict and be
sealed before any of these drafts is promoted.  No item below changes
`20/41`, constructs a `TermSource`, or attains window 15 by itself.

Static audit preparation status (2026-08-17): every one of the 22 source
drafts below now has a sibling `*Audit.draft.lean`.  A declaration-versus-
`#print axioms` comparison over Units A--F reports 173 public declarations,
173 print commands, zero missing declarations and zero extras.  This is only
coverage preparation; it is not compiler or axiom evidence.

A comment/string-stripped lightweight gate over the resulting 44 files also
reports no `sorry`, `admit`, `by?` or `exact?`, and balanced `()`, `[]` and
`{}` delimiters.  The first raw delimiter pass correctly produced one false
positive from the prose interval `(0,2*pi]`; the recorded pass excludes
comments rather than editing valid mathematical prose.

The ordered import graph has also been checked: 29 edges resolve to tracked
modules and 29 edges resolve to an earlier draft in this manifest; there are
no forward or missing imports.  This gate caught and corrected one stale
module name in Unit D.10 (`BalabanCMP89Eq251PhysicalCoordinateLine` was the
declaration concept, not a module; the tracked module is
`BalabanCMP89Eq251OneCoordinateContourShift`).

Exact-scope refresh (2026-08-17): the earlier Unit-E path list contained only
21 of the 22 declared source/audit pairs because the independent Unit-A
`BalabanCMP89CenteredBrillouinAffineSlice` pair was omitted.  The pair is now
restored to the path list rather than silently removed from the manifest.
`tmp/STEP8B23-ALL-PATHS.txt` contains exactly 44 unique files; the overlay
guard reports `LEAN_OVERLAY_TEXT_OK files=44`.  The read-only promotion audit
reports
`STEP8B23_PROMOTION_STATIC_OK files=44 sources=22 audits=22 declarations=173 prints=173`.
All 44 bytes are frozen in `tmp/STEP8B23-SCRATCH-MANIFEST.sha256`, whose
SHA-256 is
`FA10286AE43CBA053F6B9D4A88DB6CC98ED06BA203EFD129F18C3ADF6F5FF2AE`;
the byte gate reports `44/44`.  These are static gates only, not Lean or axiom
evidence.

Deterministic promotion preview (2026-08-17):
`tmp/audit_step8b23_promotion_preview.py` transforms all 44 drafts in memory,
without writing tracked files.  It activates the 18 sibling-audit imports
that remain commented, preserves the four already-active audit imports,
inserts the mandated PRE-VALIDATION module docstring only after the last Lean
`import`, and requires every declaration sequence to remain unchanged.  It
reports

```text
STEP8B23_PROMOTION_PREVIEW_OK files=44 sources=22 audits=22 audit_imports_activated=18 declaration_files_unchanged=44 declarations=173 import_prefix_ok=44 promoted_content_manifest_sha256=ECD2671BDAFB4F4DD8A133DAC50DCD30F33EC4B88DEE3A0AF8385E0542E875DB
```

The preview-script SHA-256 is
`5404E0A6BD000381A197FA7DD4F0F6257D738E3795693A221B87FF48C53649F2`.
The promoted-content digest is a later byte-for-byte acceptance gate, not
compiler evidence and not authority to promote before Step 8b.22 is handled.

The actual promotion boundary is split, rather than writing all 44 targets at
once.  `tmp/audit_step8b23_split_promotion_preview.py` proves that Units A--E
are exactly the first 36 paths (18 source/audit pairs, 124 declarations) and
Unit F is the disjoint final eight paths (four pairs, 49 declarations); their
ordered union is the full 44-file scope.  The current deterministic results
are

```text
STEP8B23_AE_PROMOTION_PREVIEW_OK files=36 sources=18 audits=18
  declarations=124
  promoted_content_manifest_sha256=
  C1057D840543EB2EF8024B8F90B7D9B785DF7C40D5C15582E3F4E83022F41AD0
STEP8B23_F_PROMOTION_PREVIEW_OK files=8 sources=4 audits=4
  declarations=49
  promoted_content_manifest_sha256=
  AEC2A745A059DBFA7F24F8F52233156F9569ECF8AF35329292B0F3BDDCA7C619
STEP8B23_SPLIT_PROMOTION_PREVIEW_OK ae_files=36 f_files=8 union=44
  overlap=0 declarations=173
```

The split-preview script SHA-256 is
`22AE11267EA06DD2BDCE0C02340EEE2B172CCB51AC50CD90B9360D57D29ACD55`.
Consequently a later writer must promote A--E first; Unit F remains scratch
until item 18 has its own cold seal.  The aggregate 44-file preview is a byte
gate only and is not authority to violate that order.

The restartable order is independently checked by
`tmp/audit_step8b23_brick_schedule.py`.  It requires the 22 module names below
to equal the exact 44-file scope, checks ordered declaration/print equality,
and rejects any internal import whose producer occurs later in the declared
queue.  The current result is

```text
STEP8B23_BRICK_SCHEDULE_OK bricks=22 declarations=173 internal_dependencies=29 schedule_sha256=DE4FAFAEB1399540D48A6900536F56C6ABCF2DA68E60833D7979CE4486725AA9
```

The script prints the expected axiom-block count and predecessor list for
each brick; its SHA-256 is
`190F30A3E731D0864D0D145860885B7162BDBB67F1D34C0F166C6AA9D5F39F1B`.
This is a scheduling gate only, not elaboration evidence.

Runner-generation preparation (2026-08-17):
`tmp/generate_step8b23_ae_validation_runner.py` is a fail-closed generator
for the later Units A--E Colab runner.  It cannot run successfully before the
36 promoted files have been committed: it reads every byte through
`git cat-file blob SOURCE_SHA:path`, requires the PRE-VALIDATION mark in all
36 blobs, rejects placeholder tokens, fixes the 18-brick dependency order
above and assigns the exact 124 expected axiom blocks.  Unit F is absent by
construction.  Its current lightweight static check reports

```text
STEP8B23_AE_RUNNER_GENERATOR_STATIC_OK bricks=18 files=36 axiom_blocks=124
  sha256=D40EFF3ADCF4D5CF3064E6876C7FFB81649B0001D5E5013EEE0829BE36AFE1D1
```

This generator is scratch preparation only.  It neither promotes source nor
authorizes a Colab/CI run; the generated runner becomes meaningful only after
Step 8b.22 is terminally classified and the A--E source checkpoint exists.

The companion
`tmp/generate_step8b23_ae_terminal_workflow.py` prepares the one allowed cold
terminal run.  It deliberately rewrites the already-default-branch-visible
workflow path `.github/workflows/validate-localized-carrier.yml`; creating a
new workflow path on the draft branch would reproduce the dispatch-time 404
already measured in this campaign.  The generated workflow checks all 36 Git
blobs, exact toolchain and Mathlib pins, runs 18 focal/audit pairs
stop-on-first-error, requires 124 allowed axiom blocks, and emits a
deterministic evidence archive.  Its current SHA-256 is
`C4A902D027B98047916187BD1F55A19FC48653B95855E170E79F7314D641F415`.
The generator now exposes the same workflow body through a parameterized
scope function; the A--E self-test below proves that its 36-file/124-block
contract is unchanged.

`tmp/test_step8b23_ae_generators.py` compiles both generated Python payloads,
compiles the embedded workflow axiom verifier, checks the exact
36-file/18-brick/36-stage/124-block scope, proves Unit F absent, and exercises
fail-closed behavior when a source blob lacks PRE-VALIDATION.  It reports

```text
STEP8B23_AE_GENERATOR_SELFTEST_OK runner=pass workflow=pass
  tamper=fail_closed files=36 bricks=18 stages=36 axiom_blocks=124
```

Its SHA-256 is
`D2D0607BAC24EA6545B68F7D7BD2FB2E1F107BF3DE7C3CFE1466408FDE7F3145`.
These checks remain transport/instrumentation preparation, not Lean evidence.

Cold-evidence acceptance is likewise prepared before compute.
`tmp/audit_step8b23_ae_cold_evidence.py` independently reconstructs the 36
expected blob hashes from `git cat-file`, checks exact source/workflow SHAs,
cold mode, toolchain and Mathlib pins, ordered path scope, all 36 child exits,
18 literal final build sentinels, 124 allowed axiom blocks, the recorded axiom
JSON, `FINAL_STATUS`, every `SHA256SUMS` entry, the deterministic inner tar and
the raw outer artifact ZIP byte-for-byte.  Its SHA-256 is
`38C2254FEF47FF3D66914E172507F54CB8888ECEF50CCE72D26C0BE6402DC3B2`.
Its scope/count implementation is parameterized without changing the A--E
contract, so the same fail-closed archive checks can be reused for Unit F.
The synthetic positive/tamper test
`tmp/test_step8b23_ae_cold_evidence.py` reports

```text
STEP8B23_AE_COLD_EVIDENCE_SELFTEST_OK positive=pass tamper=fail_closed
  stages=36 axiom_blocks=124
```

and has SHA-256
`AEED94A39ADEF4035CA1E8E324A6CCE760B1242206BEAA3F3CF9456D65F1DDE7`.
No result from these validators can substitute for the later cold artifact.

The final mechanical boundary is prepared in
`tmp/promote_step8b23_ae.py`.  It requires an explicit expected HEAD, a clean
tracked worktree and index, both Step-8b.22 files equal the exact certified
sealed bytes (not merely missing a marker), the audit imported by
`YangMillsCore.lean`, the immutable run/source identity recorded in both the
vertical map and ledger, all 36 targets absent, and the exact A--E
promoted-content digest
`C1057D840543EB2EF8024B8F90B7D9B785DF7C40D5C15582E3F4E83022F41AD0`.
Writing requires the additional `--write` flag and verifies every byte after
materialization.  Unit F is unreachable from this script.  The current
read-only plan check reports

```text
STEP8B23_AE_PROMOTION_PLAN_OK files=36
  manifest=C1057D840543EB2EF8024B8F90B7D9B785DF7C40D5C15582E3F4E83022F41AD0
STEP8B23_AE_PROMOTION_GATE_OK current_state=blocked_until_step8b22_seal
  first_error=STEP8B22_SEALED_BLOB_MISMATCH
```

The script SHA-256 is
`453B745EAA3A5CC55A83C0859EDD18F2F36D20B9061B2529A1B623E47B409105`.
The blocked result is intentional and prevents promotion from racing the
current terminal Step-8b.22 classification.

After the later external terminal verdict,
`tmp/retrieve_step8b23_ae_cold_evidence.ps1` provides the fail-closed
retrieval path.  It requires the completed successful run, exact workflow
vehicle SHA, authenticated `lluiseriksson` account and one exact artifact;
retains the raw binary ZIP separately from `gh run download`; and invokes the
independent validator above with source/workflow SHAs.  It refuses an existing
destination and has been parser-checked without network execution:

```text
STEP8B23_AE_RETRIEVER_PARSE_OK
  sha256=620759D7F613E460FDB672C04B24EB2FB127BB542A1C681102BDCEB380D63577
```

The retriever is not to be run before that external terminal verdict.

Unit F has its own mechanical gate rather than inheriting authority from the
aggregate 44-file preview.  `tmp/promote_step8b23_f.py` requires exact HEAD
and clean tracked state, compares all 36 A--E targets against their expected
**sealed** bytes (PRE-VALIDATION removed) with prerequisite digest
`07C83157A79B64A12F5135423F86F76252E092CD185D0D58FDF61694A34C1978`,
requires every A--E audit already imported by `YangMillsCore.lean`, requires
the eight F targets absent, and writes only those eight under the
explicit `--write` flag.  Their PRE-VALIDATION promotion digest remains
`AEC2A745A059DBFA7F24F8F52233156F9569ECF8AF35329292B0F3BDDCA7C619`.
Current read-only checks report

```text
STEP8B23_F_PROMOTION_PLAN_OK prerequisites=36 new_files=8
  manifest=AEC2A745A059DBFA7F24F8F52233156F9569ECF8AF35329292B0F3BDDCA7C619
STEP8B23_F_PROMOTION_GATE_OK
  current_state=blocked_until_36_AE_prerequisites_sealed
  first_error=SEALED_AE_PREREQUISITE_MISSING
```

The writer SHA-256 is
`6C64067F9F1F7653CA60821D41886163D4CA338484CBB6ACE8216AA0C8E1E734`.
The refusal in the present tree is intentional and prevents Unit F from
racing the A--E cold seal.  The two repaired promotion gates were exercised
together against the current head in 0.361 s with a 23,814,144-byte peak
working set; both rejected at their first absent/unsealed prerequisite and
left the tracked tree unchanged.

The Unit-F diagnostic runner is prepared separately in
`tmp/generate_step8b23_f_validation_runner.py`.  It requires all 36 A--E
prerequisite blobs to equal their sealed bytes, all eight Unit-F blobs to
retain PRE-VALIDATION, and fixes the four source/audit pairs, eight child
stages and 49 expected axiom blocks.  The cold terminal companion
`tmp/generate_step8b23_f_terminal_workflow.py` reuses the parameterized A--E
workflow body, verifies all 44 blobs, and compiles only those four Unit-F
pairs.  It therefore cannot reinterpret a partial A--E seal as authority for
Unit F.  The synthetic companion
`tmp/test_step8b23_f_runner_generator.py` compiles the generated payload,
compiles the embedded workflow axiom verifier, checks the exact scope and
proves fail-closed behavior after restoring a PRE-VALIDATION mark in one
prerequisite.  Its current result is

```text
STEP8B23_F_RUNNER_SELFTEST_OK runner=pass workflow=pass prerequisites=36
  unit_f_files=8 bricks=4 stages=8 axiom_blocks=49
  unsealed_tamper=fail_closed
  generator_sha256=4E348D31A415CF570FB6164FF3EE0C7397B595DC1DD49E332ECFBA3683000644
```

The diagnostic generator SHA-256 is the value printed above; the terminal
workflow generator SHA-256 is
`85DE3DA58B34773DD40B2931C6D64350A398E41D9DC435A68044A2FC14DB09ED`;
the test SHA-256 is
`6996E2BDA3C3A66E397B7AB3452697740D33A9D49A8C8E4B534027A01512A92F`.
This is diagnostic instrumentation only, not Lean/compiler evidence and not
authority to run Unit F before the A--E seal.

Post-hardening regression (2026-08-17): all eight static promotion previews,
brick-schedule checks, A--E/F runner generators and synthetic cold-evidence
validators passed together in 1.938 s with a 31,145,984-byte peak working set.
The measured scope remains 44 files, 22 bricks, 173 declarations/readouts and
29 topological internal dependencies.  This regression did not invoke Lean,
Lake, GitHub or any network service and is not compiler evidence.

Unit-F cold-artifact acceptance is independently exposed by
`tmp/audit_step8b23_f_cold_evidence.py`.  It fixes the 44-file blob scope,
four focal/audit pairs, eight ordered stages, 49 allowed axiom blocks and the
`step8b23-f-evidence.tar.gz` inner archive.  Its synthetic companion proves a
complete positive fixture and fail-closed behavior after changing the
recorded terminal status:

```text
STEP8B23_F_COLD_EVIDENCE_SELFTEST_OK positive=pass tamper=fail_closed
  files=44 stages=8 axiom_blocks=49
```

The Unit-F validator SHA-256 is
`C899C6A323F662C2AAF9B3AAF51EA0BC295273F954EC160BBB296DBB40158ED6`;
the test SHA-256 is
`334AC72E0C4479DDE446C355ACB31E6A77197F48B008444A52096462EFA3EBD1`.
This remains instrumentation evidence only; a real cold artifact is still
required before Unit F can be sealed.

The later retrieval path is frozen in
`tmp/retrieve_step8b23_f_cold_evidence.ps1`.  It refuses a nonterminal or
non-successful run, a workflow-SHA mismatch, the wrong authenticated GitHub
account, an ambiguous artifact name or an existing destination.  It retains
the raw binary ZIP, independently downloads the extracted artifact and calls
the Unit-F validator above.  Parser-only validation reports

```text
STEP8B23_F_RETRIEVER_PARSE_OK
```

Its SHA-256 is
`1A74FAE8D3BA5C86D9534E84139DFE4751CAC64B4B649822E7C172F599692C74`.
It must not be invoked before the external terminal verdict for the later
Unit-F run.

Static semantic audit (2026-08-17): every source draft in Units A--F has
been read against the acceptance gates below.  The six unit reports record a
static PASS with explicit live hypotheses and scope boundaries:

```text
STEP8B23-UNIT-A-SEMANTIC-AUDIT.md  7CD3C3A05151D4D2DA8609E967FAEC069AB22792E3341021954AD2DA278B28D7
STEP8B23-UNIT-B-SEMANTIC-AUDIT.md  21B301287AB1568D6528E1183527D8B3424A9E2B665A9CFC28FCC849F7EE2C02
STEP8B23-UNIT-C-SEMANTIC-AUDIT.md  982C58101DADDDBEA5735E1A72000CEECEA4100DBF915CE0C7D8A2C6D82B82C4
STEP8B23-UNIT-D-SEMANTIC-AUDIT.md  79C6BB602F95B0DC87B77836147DF75E0581320FDA2EF04F430EA9B04AF02F27
STEP8B23-UNIT-E-SEMANTIC-AUDIT.md  DBEED339FD9E103276CBA48BE8DE9A8FC9C3EF8C9BB490CBA29E034360BF965B
STEP8B23-UNIT-F-SEMANTIC-AUDIT.md  CAA4D9DD6F95B789B8CCAD7BEB9F718101D070ED95865AD450767614342D2065
```

This review found no new vacuity or source-orientation defect.  It also
confirms that the final Unit-F theorem stops at the diagonal Gate-7 carrier;
the independent-scale regional dictionary, regional `B0`, window 15 and all
terminal fields remain open.  These reports are design evidence only and do
not replace elaboration or axiom audits.

## Unit A — quotient and measure foundation

Promote and validate in this order:

1. `BalabanCMP89CenteredBrillouinAffineSlice`
2. `BalabanCMP89CenteredUnitCubeTorusQuotient`
3. `BalabanCMP89CenteredTorusFourierPhase`
4. `BalabanCMP89NormalizedBrillouinToTorusMeasure`

Acceptance gates:

- the centered half-open cube covers the torus by a proved quotient map;
- the lift consumes a coordinate face-seam theorem, not an arbitrary
  `FactorsThrough` witness;
- normalized Brillouin measure is transported with its literal
  `(2*pi)^(-4)` normalization;
- the negative momentum convention and `mFourier (-n)` sign are named in
  public theorems.

## Unit B — mass-uniform Green and descended torus object

5. `BalabanCMP89Eq248GreenMassUniformHolomorphy`
6. `BalabanCMP89Eq248DisplayedGreenVectorPeriodicity`
7. `BalabanCMP89Eq248CenteredGreenTorus`

Acceptance gates:

- differentiability and every boundary-domain certificate are produced from
  the common radius, noncentral-radius, central-window and mass-window
  hypotheses;
- arbitrary integer-vector periodicity is proved for the displayed finite
  sum, not postulated for the stabilized quotient;
- continuity and every coordinate face seam of the literal Green are
  derived internally before quotient descent.

## Unit C — exact finite sample dictionary

8. `BalabanCMP99CenteredTorusSampleDictionary`
9. `BalabanCMP99CenteredTorusPhysicalGreenSampleTransport`

Acceptance gates:

- the positive sample `ell/N'` uses the centered representative
  `-a_ell/N'`;
- `mFourier n` at that sample is proved equal to the positive finite
  `ZMod` character;
- the nonzero branch constructs `unit`, `reduced` and complete `fine`
  nonvanishing at both centered and uncentered momenta;
- transport exits to the displayed Green before applying the integer-vector
  period and re-enters the stabilized quotient only on the physical domain;
- the `ell = 0` branch is separate and does not cancel a zero central
  symbol;
- no Fourier-negation rewrite appears in the sample theorem.

## Unit D — contour equality and physical coefficient bound

10. `BalabanCMP89Eq248GreenOneCoordinateContourShift`
11. `BalabanCMP89Eq248GreenProductContourTelescope`
12. `BalabanCMP89Eq248MassUniformGreenBound`
13. `BalabanCMP89Eq248MassUniformNormalizedGreenBound`

Acceptance gates:

- each one-coordinate shift consumes the Green-specific holomorphy and face
  seam; no integral equality is an input;
- four-coordinate telescoping constructs integrability on the compact cube
  internally;
- the pointwise majorant is for the literal stabilized numerator and
  denominator;
- source normalization cancels the Brillouin-cube volume exactly;
- the public decay is in physical fine displacement and does not yet claim
  a regional `B0`.

## Unit E — actual Fourier coefficients and Step 8b.22 consumption

14. `BalabanCMP89CenteredTorusGreenCoefficientPhase`
15. `BalabanCMP89CenteredTorusGreenCoefficientDictionary`
16. `BalabanCMP89SignedLatticeL1TotalSum`
17. `BalabanCMP89CenteredGreenFourierSummability`
18. `BalabanCMP99PhysicalGreenFiniteGridAliasing`

Acceptance gates:

- every reciprocal alias phase at integer displacement is discharged by the
  sealed physical-period theorem before lifting through the finite sum;
- the coefficient dictionary is proved pointwise on the physical cube and
  then almost everywhere under the restricted measure; it asserts nothing
  off the cube;
- the signed `l1` exponential sum is used at the owner rate, without a
  spurious `(L^j)^4` volume factor; this gate proves absolute summability for
  reconstruction but does not by itself retain periodic owner decay;
- Fourier reconstruction consumes the actual `mFourierCoeff` summability,
  not a supplied family equality;
- the final theorem has the literal uncentered CMP99 Green samples on its
  finite-DFT side and the literal normalized fine Green coefficients on its
  residue-class side.

## Unit F — post-aliasing periodic owner decay

This unit is downstream of the 18-module Step 8b.23 aliasing seal and must not
be folded into its counter.  Promote only after item 18 is cold-sealed:

19. `BalabanCMP89CenteredPeriodicL1ResidueSum`
20. `BalabanCMP99CenteredPeriodicEndpointDictionary`
21. `BalabanCMP99PhysicalGreenZeroResidueBound`
22. `BalabanCMP99DiagonalFiniteGreenOwnerBound`

Acceptance gates:

- the one-dimensional proof uses `2*|u_c| <= P` and preserves the factor
  `exp (-delta*|u_c|)`;
- the `d`-dimensional theorem is a literal product estimate, not a ball-count
  surrogate;
- at `delta = rho/K`, `P = K*N`, the constant is uniform in `N` and no
  `(K*N)^d` factor appears;
- the physical endpoint representative and its integer carry are built
  canonically from the signed centered-alias equivalence;
- the residue-zero selector is reindexed by a named translation equivalence;
- the literal mass-uniform Green coefficient bound is constructed internally
  and the norm of the selected complex coefficient sum is bounded by the
  centered periodic majorant;
- the final Unit-F theorem converts that centered length to the owner metric
  only on `FinBox 4 (K*N)` with owner side `K`, retaining the explicit
  `exp (2*rho)` boundary factor;
- none of these modules claims a regional owner metric, `B0`, `||R'|| < 1`, or
  window-15 attainment.

The next consumer must identify the centered representative length with the
periodic owner metric on the **diagonal Gate-7 carrier** and combine the
literal Green coefficient bound with Step 8b.22.  This closes item 4 only.
The separately recorded item-5 dictionary must then replace the diagonal
`K = L = M` carrier by independent source scales `(L,K)` before the sealed
source-localization-owner bridge can be applied.  Only after that
scale-separation step can regional compression and the physical `B0`
producer begin.

## Audit and sealing rule

Each promoted module receives a sibling audit containing `#print axioms` for
every public theorem and noncomputable definition that is used downstream.
Expected output is exactly the standard trio
`[propext, Classical.choice, Quot.sound]` or a strict subset.  Any
`sorryAx`, `ofReduceBool`, project axiom, missing declaration, warning or
nonzero child exit is a failing gate.

Diagnostic cache restoration is allowed.  Removal of `PRE-VALIDATION`, map
status changes and source-ledger sealing require the cold terminal checkout
for the exact source checkpoint.  The final Step 8b.23 seal must cite the
source SHA, toolchain, Mathlib pin, focal exit, audit exit, axiom count,
literal job count and durable artifact hashes.
