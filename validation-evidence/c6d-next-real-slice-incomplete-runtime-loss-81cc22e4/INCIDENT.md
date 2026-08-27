# C6d next real-slice cold gate — INCOMPLETE-RUNTIME-LOSS

- mathematical source: `81cc22e41d46cce150c2a263c85e4acb90087153`
- runner checkpoint: `300faf158314faa8c360cb4ad8527bf7e1f034a4`
- notebook checkpoint: `8106025057c4fac4e1e59a4e5b594f492ff1af4a`
- runner revision: `c6d-next-real-slice-v3`
- runtime opened: `2026-08-27T19:25:36.952921+00:00`
- classification: `INCOMPLETE-RUNTIME-LOSS`; neither PASS nor FAIL

The visible prefix compiled the pinned dependency graph (`8554` jobs) and the
three focal source/audit pairs, then entered
`STAGE=c6d_next_real_slice_root CMD=["lake", "build", "YangMillsCore"]`.
The browser later lost its runtime connection.  On reconnecting, a separate
read-only diagnostic cell reported:

```text
C6D_RECOVERY_DIAG_V1=1
ROOT_EXISTS=False
LAKE_EXISTS=False
ROOT_OLEAN_EXISTS=False
ARCHIVE_EXISTS=False
PROCESS_LIST_BEGIN
PROCESS_LIST_END
C6D_RECOVERY_DIAG_DONE=1
```

No evidence archive, checkout, cache, root result, or live process survived.
The prefix is retained only as incident information.  It is not compiler
evidence, does not retire PRE-VALIDATION, and does not move `20/41` or
`TermSource = 0`.

An immediate recovery attempt was assigned a standard `12.67 GiB` CPU
runtime instead of the required high-RAM runtime.  The runner stopped before
checkout or Lean with literal `HIGH_RAM_REQUIRED` and recorded:

```text
EVIDENCE_SHA256=4f1a31d02342da34d02794ed2b499f1fc3d39ac276be1c17af716a5d4b087e74
EVIDENCE_ARCHIVE_SHA256=279ce48dfbb7872effffda7cca936d8b150b534fc30b5821909a865becb1985d
FINAL_STATUS=FAIL
```

This second event is `BLOCKED-HIGH-RAM` instrumentation evidence, not a
mathematical failure.  Colab was then explicitly switched to CPU with the
high-RAM option before any further launch.
