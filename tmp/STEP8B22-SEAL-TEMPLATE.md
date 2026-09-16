# Step 8b.22 seal template — do not apply before artifact audit

Status: scratch only.  This is not compiler evidence and does not authorize
retirement of either PRE-VALIDATION header.

## Immutable identity

* Run/job: `31991954503` / `95276977132`.
* Workflow HEAD: `b05ef65af97a95752d1c929e30749d886d425d8d`.
* Exact source: `534493728038813f3772f8b3b073237f4da1884e`.
* Source/audit Git-blob SHA-256:
  `de04ca53ce8b753e80514e607f0b47ae6c6cf41811b353e60030b21f4a5a2a52` /
  `1207c5881c98379753407f426392100b08e44c503d64ce03cc2c3daba7b5290b`.
* Expected source/audit bytes after removing only the two authorized
  PRE-VALIDATION paragraphs:
  `C82E0BB9D43BECE07C5660E7D3170F2289EBC4188969C222ABC6647C9F0EC34A` /
  `9B804AFB964B08EED9A2B7910C8013F29BC326FAE5324C55F4130EB6F5A89785`.
* Expected artifact:
  `cmp99-finite-grid-aliasing-534493728038813f3772f8b3b073237f4da1884e`.

## Values that must come from the downloaded artifact

* focal exit/time/jobs: `<FOCAL_EXIT>` / `<FOCAL_SECONDS>` /
  `Build completed successfully (<JOBS> jobs).`
* audit exit/time: `<AUDIT_EXIT>` / `<AUDIT_SECONDS>`.
* axiom blocks: exactly seven; record each measured set, never infer it from
  the source.
* evidence-manifest (`SHA256SUMS`) SHA-256: `<EVIDENCE_MANIFEST_SHA256>`.
* raw GitHub artifact ZIP SHA-256: `<OUTER_ARTIFACT_ZIP_SHA256>`.
* deterministic uploaded evidence tarball SHA-256:
  `<INNER_ARCHIVE_SHA256>`.
* verified manifest entry count: `<MANIFEST_COUNT>`.
* final sentinel: literal `FINAL_STATUS=PASS`.

## Exact tracked delta on PASS

1. Remove only the two PRE-VALIDATION paragraphs from
   `BalabanCMP99FlatFiniteGridAliasing.lean` and its sibling audit.  Require
   the resulting two byte hashes above; any other source/audit edit rejects
   the seal.
2. Change the Step-8b.22 vertical-map state from PRE-VALIDATION/NOT CHECKED
   to SEALED and append the measured run values above.
3. Add ledger Addendum 867 containing the same immutable identity and
   measurements.  Preserve the earlier v1 focal failure and both v2
   `INCOMPLETE-RUNTIME-LOSS` attempts as non-evidence; do not rewrite them as
   compiler failures or passes.
4. State the delimitation literally: generic finite-grid aliasing only.  The
   physical Fourier-series expansion, regional `B0`, window 15, terminal
   fields and `TermSource` remain open.
5. Keep counters exactly `20/41`, `TermSource = 0`; window 15 remains
   compatible but unattained.

If any required artifact value is absent or any hash/manifest check fails,
do not apply this delta.
