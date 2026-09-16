# Step 8b.22 cold seal checklist

Status: prepared from the tracked workflow at `b05ef65a`; not evidence that
run `31991954503` passed.

## Immutable inputs

* Workflow run: `31991954503`, job `95276977132`.
* Workflow HEAD: `b05ef65af97a95752d1c929e30749d886d425d8d`.
* Exact source: `534493728038813f3772f8b3b073237f4da1884e`.
* Source blob SHA-256:
  `de04ca53ce8b753e80514e607f0b47ae6c6cf41811b353e60030b21f4a5a2a52`.
* Audit blob SHA-256:
  `1207c5881c98379753407f426392100b08e44c503d64ce03cc2c3daba7b5290b`.
* Mathlib pin: `07642720480157414db592fa85b626dafb71355b`.
* Lean asset SHA-256:
  `bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e`.
* Expected artifact:
  `cmp99-finite-grid-aliasing-534493728038813f3772f8b3b073237f4da1884e`.

## Acceptance gate

Do not seal from the GitHub job summary alone.  Download the artifact and
require all of the following from its contents:

Preserve both transport layers.  `gh run download` extracts the artifact and
therefore cannot supply the outer ZIP digest by itself.  After the external
watcher reports a terminal conclusion, resolve the artifact id from run
`31991954503`, download the raw `/artifacts/{id}/zip` endpoint with `gh api`,
and separately extract/download its contents.  Under Windows PowerShell 5.1,
use binary `cmd.exe` redirection for the raw `gh api` response; PowerShell's
text redirection can corrupt a ZIP.  No token is placed on the command line
because `gh api` uses the authenticated keyring directly.

```powershell
$artifactName = 'cmp99-finite-grid-aliasing-534493728038813f3772f8b3b073237f4da1884e'
$artifactId = gh api repos/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/31991954503/artifacts `
  --jq ".artifacts[] | select(.name == `"$artifactName`") | .id"
if (-not $artifactId) { throw 'Expected artifact not found' }
$rawZip = '<evidence-dir>\step8b22-github-artifact.zip'
cmd.exe /d /c "gh api repos/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/artifacts/$artifactId/zip > `"$rawZip`""
gh run download 31991954503 --repo lluiseriksson/THE-ERIKSSON-PROGRAMME `
  --name $artifactName --dir '<evidence-dir>\extracted'
python tmp/audit_step8b22_cold_evidence.py `
  --artifact-root '<evidence-dir>\extracted' --outer-zip $rawZip
```

1. `checkpoint.txt` records exact source, workflow SHA and `COLD_MODE=true`.
2. Toolchain URL/digest and executable hashes are present; Lean/Lake versions
   match `v4.29.0-rc6`.
3. `mathlib.txt` records the exact pin above; manifest/toolchain hash guards
   did not permit mutation.
4. Text and import-prefix guards exit zero on exactly the source/audit pair.
5. `stages.txt` records focal and audit exit zero.
6. Focal log ends with one literal `Build completed successfully (... jobs).`
   line and has no new-module linter warning for the source path.
7. Audit log contains exactly seven nonempty axiom blocks, every set a subset
   of `{propext, Classical.choice, Quot.sound}`, and neither `sorryAx` nor
   `ofReduceBool` occurs.
8. `FINAL_STATUS` is literally `FINAL_STATUS=PASS`.
9. Every line in `SHA256SUMS` verifies; the deterministic inner archive hash
   agrees with `ARCHIVE_SHA256`.
10. The raw GitHub artifact ZIP is retained and hashed independently from the
    uploaded deterministic `cmp99-finite-grid-aliasing-evidence.tar.gz`.

Run `tmp/audit_step8b22_cold_evidence.py --artifact-root <extracted> --outer-zip
<raw.zip>` over the two retained objects.  A seal requires its literal
`STEP8B22_COLD_EVIDENCE_OK` output.  The script independently checks the
checkpoint, toolchain, Mathlib pin, exact guards, stage exits/timestamps,
final build line, seven measured axiom blocks, sentinel, every manifest entry,
inner-archive contents and both archive digests.  Prepared script SHA-256:
`0EF27485E60F771EBB2FE2D0AA7B26A20D73AC6DB81C3E8ED77D52F622AFD040`.
The validator also requires exact member/byte equality between the raw outer
ZIP and the extracted artifact.  Its synthetic positive/tamper self-test
reports
`STEP8B22_COLD_EVIDENCE_SELFTEST_OK positive=pass tamper=fail_closed`;
the self-test SHA-256 is
`1577676FC20C2B99A592D63A552202BDA8A7FBD756DDB6629E053C75D96BACFC`.

Any missing item is incomplete evidence, not a PASS inferred from the
visible prefix.

The same retrieval is encoded fail-closed in
`tmp/retrieve_step8b22_cold_evidence.ps1`.  It refuses to overwrite an
existing destination, verifies the authenticated GitHub account, requires
exactly one artifact with the immutable name above, preserves the raw ZIP by
binary `cmd.exe` redirection, downloads the extracted artifact separately and
runs the independent validator.  The script has been parsed without
execution; SHA-256 is
`4384DC029EBDE7F012312719C9F6F9971182012DFA782983478EF4BB4219A330`.
It must not be run before the external terminal verdict.

## Seal scope on PASS

Retire PRE-VALIDATION only from:

* `YangMills/RG/BalabanCMP99FlatFiniteGridAliasing.lean`
* `YangMills/RG/BalabanCMP99FlatFiniteGridAliasingAudit.lean`

Removing exactly those two paragraphs must produce SHA-256
`C82E0BB9D43BECE07C5660E7D3170F2289EBC4188969C222ABC6647C9F0EC34A`
and `9B804AFB964B08EED9A2B7910C8013F29BC326FAE5324C55F4130EB6F5A89785`
respectively.  These hashes are the downstream A--E promotion gate; a seal
that edits any theorem/import/proof byte is rejected.

Update the Step-8b.22 vertical-map entry and add ledger Addendum 867 with:

* exact run/job/source/workflow SHAs;
* focal jobs, stage times and exits;
* seven measured axiom sets;
* artifact id/digest, downloaded archive digest and internal manifest count;
* the earlier v1 focal failure and the two v2
  `INCOMPLETE-RUNTIME-LOSS` attempts retained as non-evidence;
* delimitation: generic finite-grid aliasing only; physical Fourier-series
  expansion, regional `B0`, window 15 and terminal fields remain open.

Counters remain exactly `20/41`, `TermSource = 0`; window 15 remains
compatible but unattained.

The exact five-file seal is also encoded fail-closed in
`tmp/seal_step8b22_from_cold_evidence.py`, SHA-256
`BCE0B360A0E92A5D10682BC39B6B3BB191D0A669121A52776BB87EC7950FC6BD`.
It reruns the independent artifact validator, requires exact workflow HEAD
`b05ef65af97a95752d1c929e30749d886d425d8d`, verifies the raw and sealed
source/audit hashes above, inserts exactly one audit import, replaces exactly
the terminal Step-8b.22 map section and appends exactly Addendum 867.  Its
synthetic positive/tamper test reports
`STEP8B22_SEAL_SELFTEST_OK positive=pass tamper=fail_closed files=5` in
0.120 s with a 28,434,432-byte peak working set.  The durable self-test
`tmp/test_step8b22_seal.py` has SHA-256
`591873B16B7E5A2D11CEC06ABBDAC7FAF5B93E9AE5B4957DA8490399941E87FE`.
The seal tool must first be run without
`--write`; the five printed post-seal hashes become part of the review gate.

## Failure path

On any terminal failure, preserve the artifact/logs and report only the first
real failing stage/error.  Do not retire marks, move counters, rerun the
workflow or promote Step 8b.24 source until that error has been diagnosed.
