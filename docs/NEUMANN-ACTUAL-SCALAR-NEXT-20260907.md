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
