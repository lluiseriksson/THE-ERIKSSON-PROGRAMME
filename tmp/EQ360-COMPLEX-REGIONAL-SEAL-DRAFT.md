# Eq. (3.60) complex regional-stencil seal draft

Status: evidence template only.  Do not copy this text into the verification
ledger or remove PRE-VALIDATION notices unless a fresh Colab archive emits
literal `FINAL_STATUS=PASS` for the exact checkpoints below and passes
`verify_eq360_complex_regional_archive.py` independently.

## Fixed gate

- source checkpoint: `[SOURCE_SHA]`
- runner checkpoint: `[RUNNER_CHECKPOINT]`
- notebook checkpoint: `[NOTEBOOK_CHECKPOINT]`
- runner revision: `[RUNNER_REVISION]`
- runner transport SHA-256: `[RUNNER_TRANSPORT_SHA256]`
- toolchain: Lean `4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`
- runtime class: Colab Pro+ CPU/high RAM

## Evidence fields

- final status: `[FINAL_STATUS]`
- focal stages / exit codes: `[FOCAL_STAGE_SUMMARY]`
- cold root jobs / seconds / exit: `[ROOT_SUMMARY]`
- audited declarations: `11`
- axiom sets: `[AXIOM_SET_SUMMARY]`
- downloaded archive SHA-256: `[DOWNLOADED_ARCHIVE_SHA256]`
- evidence input SHA-256: `[EVIDENCE_INPUT_SHA256]`
- local evidence directory: `[LOCAL_EVIDENCE_DIRECTORY]`

## Selective seal scope

The successful gate may retire exactly four PRE-VALIDATION notices from the
two source/audit pairs named by `verify_eq360_complex_regional_contract.py`.
The sealer must report `files=4 notices=4` and reject every other count.

## Proposed ledger text

## Addendum [NUMBER] ([DATE], **Eq. (3.60) complex regional stencil and compact real-slice dictionary sealed in fresh Colab Pro+; 20/41 unchanged**)

Exact source checkpoint `[SOURCE_SHA]` was validated in a fresh Colab Pro+
CPU/high-RAM checkout with Lean `4.29.0-rc6` and Mathlib
`07642720480157414db592fa85b626dafb71355b`.  Runner checkpoint
`[RUNNER_CHECKPOINT]`, revision `[RUNNER_REVISION]`, compiled the analytic
Dirichlet covariant Laplacian and its compact real-slice dictionary, their
audits, and the cold `YangMillsCore` root.  `[FOCAL_STAGE_SUMMARY]`
`[ROOT_SUMMARY]`

All 11 audited declarations use only `[AXIOM_SET_SUMMARY]`.  The runner
emitted literal `FINAL_STATUS=PASS`; the independently verified archive has
SHA-256 `[DOWNLOADED_ARCHIVE_SHA256]`.

The four-file selective seal constructs the analytic regional stencil from
zero extension, algebraic `SL(N,C)` conjugation and the inverse link, then
proves its compact real-slice equality with the physical stencil.  It does
not accept a free equality between Laplacians.  It does not yet certify the
Eq. (3.51)--(3.54) source regrouping or bound, the regional resolvent, the
four transported physical actions, uniform `B0`/`delta0`, window 15, rows
23--24, or a `TermSource`.  Counters remain exactly `20/41`,
`TermSource = 0`; window 15 remains compatible but unattained.
