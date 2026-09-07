# Actual full-solution scalar gate — PRE-VALIDATION

LIVE: one Colab launch 2026-09-07T00:13:31.101940Z, PID2214,
CPU/high RAM50.99GB, account lluiseriksson@gmail.com; HASH_GATE=PASS.
Source eb5a9ec0609b015a3d367c0d729c2c2074a45b51;
runner7343544cd9e72d14fb73fc5b740ec03bdeca86fa;
notebook/reader c9b535dd0975065da5ef29b535c7e26d955a492c.
IAB tab17, log /content/launch-neumann-actual-scalar-v1.log.
Do not reexecute. Original archive will be
/content/hrpoly-neumann-actual-scalar-diagnostic-v1-evidence.tar.gz.
Reader scripts/verify_neumann_actual_scalar_diagnostic.py. No verdict yet.
Runner/reader static contract equality passed: four stages, three exact
names (0.1063995s,18202624 observed peak RSS). Not compiler evidence.

Parent d00dfc335284b53c50e1c486afe33ac2d2de66e7.
The preceding finite-average phase diagnostic is preserved in ledger1182;
no runtime remains active from it.

Inspected literal BalabanCMP89Eq246StabilizedAliasFullSolution.lean and
the existing StabilizedAliasTransposeFullSolutionLinearity.lean. The latter
has the other orientation and remains marked PRE; it is a proof-pattern
reference, not evidence for the former. The new draft imports the actual
non-transpose source module, not that transpose lemma.

Draft tmp/NeumannActualFullSolutionScalarDraft.lean proves three proposed
identities: common scalar through the noncentral source moment, through
the total moment, and through each output coordinate. The physical index,
dimension and fibre are explicit in all signatures. No denominator is
assumed nonzero: this is homogeneity of a formula with totalized division,
not an inverse theorem at singular parameters.

The exact shipped-path text guard passed (exit0,0.1025121s); no Lean ran
on Windows. All three declarations remain compiler-unverified.
Next bounded Colab queue: prerequisites for the imported full-solution
module, draft, exact three-name axiom audit, clean-source verification.
Use first-error discipline and preserve the archive. The next mathematical
consumer is simultaneous block translation of BOTH point-source endpoints:
source phase through this constructed solution, output phase cancellation.
The target-only affine translation lemma does not supply that conclusion.
Half-cell reflection of the complete (2.46) remains separate from the
already checked phase identity of its finite-average factor.

No production promotion, uniform B0, regional inverse, or window15 claim.
20/41 and TermSource0 unchanged.

## Common-translation gate: inspected consumers, not an extra hypothesis

`BalabanCMP89Eq246FinePointSourceFibreGreen` constructs the source vector
as exp(-I*phase(aliasMomentum,sourceEndpoint)) and applies the literal
non-transpose full solution. The synthesis multiplies each output by the
opposite-sign target exponential. Neither endpoint is averaged.

`exp_I_cmp89Eq251EntireAliasPhase_latticeDisplacement` in
`BalabanCMP89CenteredTorusGreenCoefficientPhase` already quantifies over
complex base momentum and integer displacement. It removes alias periods
at integer physical shifts, not arbitrary fine shifts. Together with
`cmp89Eq251EntirePhase_physicalFine_affineResidue`, this is the named
phase route for shifts target/source -> target/source + M*n, spacing 1/M.
For the physical wrapper M=L^j, the translation is exactly one coarse
integer displacement, not one arbitrary fine site. The source multiplier
is exp(-I*phase(z,n)); target multiplier is exp(+I*phase(z,n)). Their
product is one without a real-slice or nonvanishing hypothesis.

The scalar draft must pass before its equality is lifted through the
actual point-source vector. Then cancel termwise in the output-alias sum;
only after that transport equality through the normalized integral.
Existing `cmp89UnitAddTorus_mFourier_neg_mul_stabilizedFineToFineGreen_eq_affineTarget`
moves the target alone and leaves the source unchanged; it is not this
common-translation theorem. This inspection avoids a duplicated phase
proof but supplies no new compiler evidence or half-cell reflection claim.

## Preservation recheck and next diagnostic terminology

The user-supplied 20260905 ZIP is no longer at its former Desktop path,
but the durable copy under `validation-evidence/physical-cold-hot-20260905`
was rechecked against the existing independent report: SHA-256
`69f0b70a76fe636c1e9745c2b3307ad55ddaab99dce838616037e370217e573d`,
two ZIP members, CRC check successful. This rechecks preserved bytes;
it does not add a new compiler run or a new terminal field.

The common-block HOT templates now call the prerequisite output
`parent_diagnostic_olean_sha256`, not a production output. Their parent
pins remain deliberately unset until the actual-scalar archive has a
verified PASS. Local AST and both unpinned rejection gates passed in
0.1843105 seconds with observed peak RSS 22675456 bytes; no compiler or
network ran in that test. Current Colab scalar prerequisites remain in
flight; no second execution has been launched.

## Scalar PASS preserved; bounded phase HOT launched

Scalar diagnostic now independently VERIFIED_DIAGNOSTIC_PASS, ledger1183,
preservation f1e17f75aef75fbc589136722a33a5fc7edde93d. Three exact audits,
actual draft9.199243541s; no production seal or counter change.

Common-block phase HOT source93264d4b654022f51cd1d1f0ce7963de26408d4b,
runner e5cf6e006dbcbfcd97b32e511f99253ba6a78a18,
hash d71ab21813ec71cf508618e2ea821f01f635056179b06d04379d4ca9ecb730c0.
Reader and synthetic tests196b23916: one synthetic accepted, seven
mutations rejected;0.3176427s/24297472 observed RSS. The initial synthetic
fixture used Windows path rendering for a Linux command; the exact-command
gate rejected it. Fixture corrected, no Colab run consumed by that error.

Same runtime e7dbc45c00b1, single HOT PID13365 launched
2026-09-07T00:36:57.035934UTC after the runner hash gate passed.
Log `/content/launch-neumann-common-block-phase-hot-v1.log`;
archive `/content/neumann-common-block-phase-hot-v1-evidence.tar.gz`.
Do not reexecute. Preserve original on first error or PASS. Its three
phase lemmas alone prove neither full Green covariance nor reflection.

## Exact next consumer after phase PASS (design, not compiler evidence)

The remaining common-translation composition has five finite outputs:
1. `FinePointSourceAliasVector` at source+M*n equals the original literal
   vector multiplied by exp(-I*sum(z*n)), by function extensionality and
   the source phase theorem for each alias. No free source family.
2. `StabilizedFinePointSourceSolution` has that same multiplier, by the
   scalar lemma checked in1183, not by a uniqueness/invertibility assumption.
3. `StabilizedFineToFineGreenIntegrand` is unchanged when BOTH fine
   endpoints move by M*n with spacing1/M. Rewrite each target phase and
   source solution in the finite output-alias sum, then cancel the opposite
   common factors termwise. No displacement-only (2.48) replacement.
4. Specialize to the literal physical wrapper with M=L^j and the existing
   spacing definition; do not leave M independent of the physical depth.
5. Lift the pointwise equality through
   `cmp89Eq246NormalizedPhysicalFineToFineGreen` by equality of integrands.
   This step does not require a new integrability assumption: it asserts
   equality of the already defined totalized integrals, not an inverse.

Every step keeps mass,a,z and the two endpoints of (2.46) explicit.
The final output is common BLOCK translation of the actual full Green;
arbitrary-depth half-cell reflection, regional image reconstruction and
the regional inverse identity remain separate. No new draft of these five
outputs is shipped before the pending phase diagnostic result.
