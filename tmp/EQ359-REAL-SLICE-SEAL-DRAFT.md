# Eq. (3.59) real-slice seal draft

Status: evidence template only.  Do not copy this text into the verification
ledger, remove PRE-VALIDATION notices, or move a counter unless the fresh
Colab archive for the exact source checkpoint below emits literal
`FINAL_STATUS=PASS` and passes the independent local verifier.

## Fixed gate

- source checkpoint: `08039bcbc4bc74af072bef0252d7d559cbc80fe5`
- runner checkpoint: `7af24c1a1392c300b42b63437b89d5098c273e2d`
- notebook checkpoint: `b2da8f7ad919946497ff5965168a69e98ff89711`
- runner revision: `eq359-real-slice-promoted-cold-v3`
- runner transport SHA-256:
  `8FA1989137FD558E4EB083BB3D83D529F3DAEA0DBDF3BF030BABE6491EA8404F`
- toolchain: Lean `4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`
- runtime class: Colab Pro+ CPU/high RAM

## Evidence fields to fill only after independent verification

- final status: `[FINAL_STATUS]`
- focal stages and exit codes: `[FOCAL_STAGE_SUMMARY]`
- cold root jobs / seconds / exit: `[ROOT_SUMMARY]`
- audited declarations: `[AUDITED_DECLARATION_COUNT]`
- axiom sets: `[AXIOM_SET_SUMMARY]`
- canonical evidence SHA-256: `[CANONICAL_EVIDENCE_SHA256]`
- downloaded archive SHA-256: `[DOWNLOADED_ARCHIVE_SHA256]`
- evidence manifest SHA-256: `[EVIDENCE_MANIFEST_SHA256]`
- local evidence directory: `[LOCAL_EVIDENCE_DIRECTORY]`

## Selective seal scope

The successful gate may retire exactly eleven PRE-VALIDATION notices across
the twelve source/audit files fixed by the Eq. (3.59) real-slice contract.
`BalabanCMP99ComplexLocalizedUbarBackgroundAudit.lean` is already unmarked,
so the file count and notice count intentionally differ.  The sealer must
report `files=12 notices=11` and must reject every other count.

## Proposed Addendum 946 text

## Addendum 946 ([SEAL_DATE], **Eq. (3.59) physical real-slice agreement sealed in fresh Colab Pro+; 20/41 unchanged**)

Exact source checkpoint `08039bcbc4bc74af072bef0252d7d559cbc80fe5`
was validated in a fresh Colab Pro+ CPU/high-RAM checkout with Lean
`4.29.0-rc6` and Mathlib
`07642720480157414db592fa85b626dafb71355b`.  Runner checkpoint
`7af24c1a1392c300b42b63437b89d5098c273e2d`, revision
`eq359-real-slice-promoted-cold-v3`, compiled the six source/audit pairs that
identify the compact physical background, one-scale average, generated
tower and successor background with their complex counterparts on the real
slice.  `[FOCAL_STAGE_SUMMARY]`  The cold `YangMillsCore` root completed
`[ROOT_JOBS]` jobs in `[ROOT_SECONDS]` seconds, exit `0`.

The `[AUDITED_DECLARATION_COUNT]` audited declarations use only
`[AXIOM_SET_SUMMARY]`.  The runner emitted literal `FINAL_STATUS=PASS`.
Canonical evidence SHA-256 is `[CANONICAL_EVIDENCE_SHA256]`; the downloaded
archive independently rehashes to `[DOWNLOADED_ARCHIVE_SHA256]`.  The local
evidence package has manifest SHA-256 `[EVIDENCE_MANIFEST_SHA256]`.

The selective seal retires exactly eleven PRE-VALIDATION notices across its
twelve-file scope.  It certifies the Eq. (3.59) real-slice dictionaries from
the internally generated complex tower; it does not accept a free equality
between Laplacians, towers, precisions or Greens.  It does not yet certify
the complex regional Eq. (3.60) stencil, the Eq. (3.51)--(3.54) source
regrouping and bound, the regional resolvent, a uniform `B0`/`delta0`, window
15, rows 23--24, or a `TermSource`.  Counters remain exactly `20/41`,
`TermSource = 0`; window 15 remains compatible but unattained.
