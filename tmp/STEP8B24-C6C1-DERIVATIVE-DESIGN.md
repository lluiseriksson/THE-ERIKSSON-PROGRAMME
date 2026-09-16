# Step 8b.24 / C6c.1b — mass-uniform left-derivative route

Status: static design only. No theorem proposed here has been checked by
Lean, Lake or an axiom audit.

Static D1 materialization (2026-08-17): the first source/audit pair now lives
in
`tmp/BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformHolomorphy*.draft.lean`.
It contains exactly two declarations and two matching axiom readouts.  The
lightweight text/import-prefix gates pass.  Source SHA-256:
`F6C88F8EF43DEC4E5066A9927461E7A95598629C28171180B19636B7BA59965F`;
audit SHA-256:
`07C859E25D470803AC9F2FB8FE38C8408FDBCC885B7ECA45174532EF060A37D2`.
This is still unelaborated scratch and is not compiler evidence.

Static D2 prefix materialization (2026-08-17): the one-coordinate shift and
four-coordinate product telescope now add two more source/audit pairs.  The
six-file prefix contains eight public declarations and eight matching axiom
readouts; its lightweight text and import-prefix gates pass.  Exact paths are
frozen in `tmp/STEP8B24-C6C1-PREFIX-PATHS.txt`; its digest is updated below
when D3 enters the same ordered prefix.
The new source/audit hashes are:

```text
49B197322233828D2C3D874DD4678A0758773FFF221B9EDBACE0EB7CFAAA2502
  BalabanCMP89Eq249FineLatticeLeftDerivativeOneCoordinateContourShift.draft.lean
CB0D905B4D82AFE63AFE7DCDB80E61D76D9AA34FAE51901CB685AD815344527A
  BalabanCMP89Eq249FineLatticeLeftDerivativeOneCoordinateContourShiftAudit.draft.lean
8EA1CAD775A5FAFFC1BDDC63A7D130ED917AEA93B3C4F5D69ED167A19031E5B0
  BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope.draft.lean
8EB3F893ECF643D2137B38920CBA7C5F847FB0538760A33F7FCEE56400BBA444
  BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescopeAudit.draft.lean
```

This materializes the D2 construction only.  It has not been elaborated and
does not yet supply D3's signed-contour pointwise majorant or normalized
zero-mass coefficient.

Static D3 materialization (2026-08-17):
`BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformBound*.draft.lean`
adds the mass-uniform reciprocal to the already sealed `alpha = 0` numerator,
derives the literal fine-lattice pointwise bound, constructs both the
mass-uniform normalized forward-difference equality and the normalized
signed-contour equality, and specializes the bound at `mass = 0`.  The mass
window at zero is proved by `norm_num`; it is not an input and no limit is
taken.  The complete eight-file D1--D3 prefix has 14 declarations and 14
matching readouts; its text/import-prefix gates pass.  Current path-manifest
SHA-256:
`C8A9F71F0723F914E0380A9A8038AB72510FCE602C1291995FCA4D5EF4A2E938`.
New source SHA-256:
`73F7FABE5E29917DB6275763D18BC93475B6D487AD189C5AB7FAB6FC9BB66081`;
audit SHA-256:
`5579EDAFC473FC6242922ED0490E6153191FCA251A8F768FCD8C532EA85CF929`.
This remains unelaborated scratch.  D4's generated-operator/owner transport is
still open, and no regional `B0`, window-15 or terminal conclusion follows.

Static D4a--D4b materialization (2026-08-17):
`BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativeResidueShift*.draft.lean`
now records the raw endpoint carry, its conjugated zero-residue translation
equivalence, the exact affine-residue identity and the resulting `tsum`
reindexing.  The pair has seven declarations and seven matching intended
axiom readouts.  The lightweight text/import-prefix gates pass.  Current
hashes are:

```text
941BC88EE04AA6F49BF2DC19DD24FDD7F7F542063AC9A82DFE9A98A70A833885
  BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativeResidueShift.draft.lean
FC0B642D585841CB05905C24F96ADBFEF7DA3156BEC97A5C5F8788CD9F6B7D89
  BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativeResidueShiftAudit.draft.lean
D00253F5ADC61A56214DEDEA1D84115ECFD3CFF5B628AF7472084454B0D7F36A
  STEP8B24-C6C1-D4-PATHS.txt
```

Static D4c materialization (2026-08-17):
`BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativePeriodization*.draft.lean`
adds the literal affine-residue derivative coefficient, proves full and
zero-residue absolute summability, and commutes the periodized Green
difference with subtraction and division using the new mass-uniform D3
identity.  It deliberately does not use the older tracked theorem requiring
`0 < mass`.  The pair has five declarations and five intended axiom readouts,
including a named proof that affine residue formation commutes with the
ordinary forward coordinate shift.
The combined four-file D4a--D4c path list passes the lightweight text and
import-prefix gates.  Source SHA-256:
`17D0DE2E6D94786349544CCD157DC8ED4C82468A8A311EC763D8998890DBA51D`;
audit SHA-256:
`173B71AB2EE4579118357189E6788E63F027956940EED03F1498F7769C02A783`.

Static D4d materialization (2026-08-17):
`BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative*.draft.lean`
now composes the seam reindexing, periodized difference and the generated
`G Q'^*` point-source identity.  It then proves the literal derivative
majorant, centered source-owner bound, point-source action bound and the
identity-owner localized-field upgrade without a source-cardinality factor.
The pair has seven declarations and seven intended axiom readouts.  Source
SHA-256:
`BEF71C7912F054483A56F5BDAF8012F77103A3ECB3DC79438AF7D193FF12E7C9`;
audit SHA-256:
`122ABB0BF8BE4388CF7985890CA2D77247ADFB9783C5FDCD33FFEB413563F38B`.

All six D4a--D4d files remain unelaborated scratch.  They pass only the
lightweight textual/import-prefix gates and must not be cited as compiler
evidence.  The result is still ambient and complex, not regional `B0`,
window-15 attainment or a terminal field.  No counter movement follows.

The read-only queue audit
`tmp/audit_step8b24_c6c1_derivative_static.py` fixes all seven ordered
source/audit pairs, checks declaration/readout ownership, dependency
direction, absent tracked targets and the deterministic PRE-VALIDATION
transform.  Its current output is:

```text
STEP8B24_C6C1_DERIVATIVE_STATIC_AUDIT_OK bricks=7 files=14
  declarations=33 dependencies=6
  raw_manifest_sha256=5A07EB42A187E57FB0AA137A03AF7D2DA7B629065F80C471EA11929FEB0ECEF9
  promotion_manifest_sha256=7D82089113F6ADB6058C686ABA7B994B0C6B953C953BAE0555B07A6DE2792581
  compiler_verified=false counters=20/41 term_source=0
```

The audit-script SHA-256 is
`2A63D2CDAC1F94F6C3776856DA919CD740A321947E50D0DF218FAF3C15405FA4`.
The fail-closed mechanical writer
`tmp/promote_step8b24_c6c1_derivative.py` now fixes the same 14 promoted
bytes and digest.  It additionally requires all 78 Step-8b.23/S1--C6b
prerequisites to be publicly present, free of `PRE-VALIDATION:` markers and
all 39 prerequisite audits to be imported by `YangMillsCore.lean`.  Its
SHA-256 is
`BCAD37EC8BEBC6C848C064B05AEC5C217A93FC33B57EAF278431D4C072EA78C0`.
Against exact current head `b05ef65a...` it fails closed before writing:

```text
PREREQUISITE_MISSING=YangMills/RG/BalabanCMP89CenteredBrillouinAffineSlice.lean
```

The future-state byte preview accepts exactly 14 targets with one standard
PRE marker each, while the real current-state invocation still rejects at the
first absent prerequisite.  The combined check took 0.245 s with a
23,867,392-byte peak working set.
The ordered promotion/seal contract is frozen in
`tmp/STEP8B24-C6C1-DERIVATIVE-PROMOTION-SEAL-CHECKLIST.md`, SHA-256
`48CBF98192AFFD1AE5EC65C049C1B80BD9A3D3AE7D41F858922F99E6618E3E6C`.
The future validation/retrieval instruments are now complete and frozen:

```text
A7AADB44B891501716F389DD7DA4C4B8F992F15A1DE8C4D6F831F1D1186D6795
  generate_step8b24_c6c1_derivative_validation_runner.py
5AFF3726A5759FF4CDE3D6E86C483DC23DB626FD4AB72286AC1E02CD84919483
  generate_step8b24_c6c1_derivative_terminal_workflow.py
50CA580985CE14435939445019E0ED3D8B2780E2B9142CCEEEA1BAC8E03B95B8
  audit_step8b24_c6c1_derivative_cold_evidence.py
597210E7D79363838D0E8CE672C39CFF1C5A6AD75E5BC8614A2E1A1ABED7DA8F
  test_step8b24_c6c1_derivative_runner_generator.py
1B8B370C4F683CB5DCE4EC96FBA7D28AF910767197E2972B3D389A4F74FF8996
  test_step8b24_c6c1_derivative_cold_evidence.py
8C9F8957DCF420A500636F13B67EFD979B9B91CE6293814EFC688B25ADA3FA25
  retrieve_step8b24_c6c1_derivative_cold_evidence.ps1
```

The runner/workflow and evidence self-tests pass for 14 files, seven bricks,
14 stages and 33 axiom blocks; a missing PRE marker and a tampered
`FINAL_STATUS` both fail closed.  The combined synthetic run took 0.215 s
with a 25,518,080-byte peak working set, and the retrieval script parses.
This is instrumentation only; no remote runner or Lean validation was invoked.

The explicit upstream-dependency audit is acyclic.  D3's Green-integrability
input is Step-8b.23 schedule position 11
(`BalabanCMP89Eq248GreenProductContourTelescope`), and D4d's identity-owner
reduction is Step-8b.24 position 39/C6b
(`BalabanCMP99SourceSeparatedGeneratedFlatPhysicalLocalizedFieldB0`).  Both
are earlier promotion phases and currently exist only as scratch, so D1--D4d
cannot be promoted or compiled before their cold seals.  No D1--D4d source
mentions the regional certificate, regional `left_derivative_bound`,
`TermSource`, or any terminal-field constructor; the prefix therefore does
not consume its own downstream conclusion.

## Target

Produce the zero-mass CMP89 Lemma-2.4 left-difference estimate from the
literal stabilized Green, with the same positive strip radius as the value
branch and without a caller-supplied derivative family or endpoint bound.
This is an input to the CMP96 local-action construction; it is not yet the
regional `left_derivative_bound` field of (3.42).

## Measured obstruction

The cold-sealed endpoint contour chain currently requires `0 < mass` through
the old reciprocal-denominator theorem.  The physical generated endpoint has
`mass = 0`, so those theorems cannot be specialized directly.

The obstruction is no longer mathematical at the denominator: the tracked
`norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le_massUniform` removes
the positivity premise under the existing mass window.  What is missing is
the mass-uniform propagation through holomorphy, seam, contour telescope and
normalization for the *derivative* endpoint.

## Accepted construction

Do not estimate a finite difference of the two final Green bounds. Dividing
that triangle estimate by the fine spacing loses the cancellation in (2.35).

Instead use the tracked exact identity

```text
cmp89Eq248ComplexStabilizedGreenEndpoint_forwardDifference
```

at every complex momentum. It identifies the derivative integrand with the
literal divided difference before any norm is taken. Consequently:

1. Differentiability of the derivative integrand follows from the two
   mass-uniform Green endpoint functions by subtraction and division by the
   nonzero fine spacing.
2. The vertical-face seam follows by applying the mass-uniform Green seam to
   the original and forward-shifted integer endpoints and subtracting the two
   equalities.
3. The one-coordinate Cauchy shift then uses the existing rectangular shift
   theorem with those two internally proved facts.
4. Product integrability follows from continuity of the same exact divided
   difference; it is not accepted as a field.
5. Four coordinate shifts telescope exactly as in the cold-sealed positive-
   mass endpoint chain.
6. The signed-contour pointwise numerator bound and the mass-uniform
   reciprocal bound give the normalized source integral with no volume loss.

## Restartable bricks

### D1 — mass-uniform derivative holomorphy and seam

Public conclusions:

- differentiability at every point of the common polydisc for the literal
  `cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand`;
- physical `2*pi` boundary seam for the same literal integrand.

Required inputs are exactly `ha`, `rho >= 0`, the amplitude/radius/window
conditions, the mass window, cube real-part bounds and polydisc imaginary-part
bounds.  The literal spacing is not a free argument: it is
`cmp89Eq249FineLatticeSpacing L j`, and `[NeZero L]` proves it positive inside
the already sealed forward-difference identity.  Thus the denominator fact is
live and derived, rather than reintroduced as a caller premise.  There is no
`0 < mass` premise.

### D2 — mass-uniform derivative contour telescope

Public conclusions:

- one-coordinate interval-integral shift;
- partial-product integrability;
- stage-to-successor equality;
- four-coordinate real-to-signed contour equality.

No slice equality, integrability certificate or family of stage functions is
accepted from the caller.

### D3 — normalized zero-mass endpoint coefficient

Specialize D2 to `mass = 0` and the generated positive coefficient `a`, then
prove the normalized Brillouin integral bound using the existing exact
translated-cube normalization. The conclusion retains the literal signed
`l1` decay and the explicit endpoint amplitude.

### D4 — generated operator/owner transport

Identify D3 with the forward difference of the generated `G Q'^*` endpoint,
then repeat the finite-grid/owner dictionary without changing Fourier
orientation. The output is the source-owner localized derivative analogue of
C6b. It remains ambient and complex; CMP89 (2.34)/CMP95/CMP96 perform the
regional transport later.

Static dependency audit (2026-08-17): this is not a single definitional
rewrite.  The prepared value branch identifies a generated point-source value
with a zero-residue sum of
`cmp89Eq248CenteredGreenPhysicalFourierCoefficient`; D3 bounds the forward
difference of each underlying normalized Green coefficient.  Passing between
them requires the following finite chain.

1. **D4a — interior endpoint shift.**  Away from the periodic seam, prove that
   replacing the fine target `x` by `x.shift mu` changes the literal negative
   fine-to-coarse endpoint displacement by
   `cmp89Eq248FineLatticeForwardCoordinateShift mu`.  This is an equality of
   the actual endpoint functions, not a caller dictionary.
2. **D4b — seam reindexing.**  At the wrap seam the integer representatives
   differ by `1 - fineSide`, not by `1`.  Reindex the zero-residue subtype by
   the corresponding coordinate multiple of the coarse side and prove that
   the affine physical residue is nevertheless the same forward-shifted
   endpoint.  The bijection and its two inverse laws must be explicit; no
   signed-vector equality across the seam is admissible.
3. **D4c — periodized forward difference.**  Use absolute summability to
   transport subtraction/division through the two zero-residue `tsum`s,
   apply the tracked normalized-Green forward-difference theorem termwise,
   and obtain the derivative zero-residue sum.  Step 8b.22 supplies only the
   generic finite-grid aliasing algebra; the physical coefficient and
   summability inputs come from the source-specific Step 8b.23/8b.24 value
   branch and must remain visible.
4. **D4d — generated point source and owner bound.**  Rewrite both generated
   endpoint values using the constructed point-source identity, then combine
   D3's literal `l1` majorant with the centered endpoint/owner dictionary.
   Extend from one point source to the same identity-owner fibre used by C6b,
   without a fine-volume or source-cardinality factor.

The missing object after this audit is therefore the seam-aware periodized
forward-difference dictionary D4a--D4c.  It is new exact finite-torus algebra,
not an analytic hypothesis and not permission to accept an equality from the
caller.  None of D4a--D4d has been elaborated or compiler-verified.

## Acceptance gates

- `mass = 0` is an actual specialization, not a limiting hypothesis.
- The derivative integrand is definitionally/literally the tracked CMP89
  endpoint, not a new function with an assumed equality.
- The divided-difference cancellation occurs before norms.
- Positivity of the generated fine spacing is consumed in the exact
  divided-difference theorem from `[NeZero L]`; it is neither a caller premise
  nor inferred from an unrelated scale window.
- Both endpoint seams are proved separately; no shared sign is assumed.
- The periodic target seam is handled by a proved residue-class reindexing;
  the raw integer displacement is not claimed to advance by one there.
- `tsum` subtraction and the residue-class change of variables are justified
  by the already constructed absolute-summability witnesses.
- The same `rho` and scalar windows as the value branch are used.
- No fine-volume, source-fibre-cardinality or extra `L^j` factor enters the
  primitive (2.35) bound.
- The final D4 estimate is not labeled regional `B0` and does not move
  `20/41`, window 15 or `TermSource`.
