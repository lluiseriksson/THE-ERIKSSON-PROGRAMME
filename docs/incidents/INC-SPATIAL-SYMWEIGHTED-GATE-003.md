# INC-SPATIAL-SYMWEIGHTED-GATE-003

Date: 2026-08-01

## Intended repair

Rerun the unchanged normal-mode symbolic judge using the long-build pattern
from `CLAUDE.md`: a detached hidden PowerShell process, persistent log, durable
completion sentinel, and polling windows no longer than 45 seconds.

The gate remained fixed at raw commit
`06226edc9221fa60a6ed39e30ae84c848bd66041`, SHA-256
`a95e66da0ee527b1776ceb3d13d83760d1fd88cc9227ebea668a2b98ca1946cf`.

## Measured run

The hidden PowerShell wrapper was PID 16776.  Its Python judge child was PID
21364, command
`python scripts/judge_spatial_symweighted_factorization.py`, started at
`10:48:06+02:00`.  Four polling windows of at most 40 seconds did not interrupt
the process.  The judge completed at approximately `10:51:21+02:00`.

The persistent 297-byte log contains valid JSON:

```json
{"classification": "exact symWeighted ring/dual factorisation gate only", "configuration_pairs_checked": 5460, "ring_sizes": [1, 2, 3, 4, 5, 6], "scale_mutations_rejected": 5460, "source_closing_bond_mutations_rejected": 5460, "status": "PASS", "target_closing_bond_mutations_rejected": 5460}
```

PowerShell independently parsed the JSON and verified all four counters equal
5460.  The log SHA-256 is
`3e0285540203254ae82c312cf9ef037e134747f76a2dadeb9fcd02dab546b293`.

## Remaining infrastructure defect

The wrapper created `normal.done.json` at the completion time but left it at
zero bytes.  Consequently this run did not durably recover the native Python
exit code, despite preserving the complete PASS output.  The next runner must
write the sentinel atomically (temporary file followed by rename), include its
own PowerShell errors in a separate wrapper log, and verify nonzero sentinel
length before declaring completion.

Under the global single-build-token instruction, optimised mode was not
started.  Therefore the full two-mode gate is not certified and the one Lean
theorem remains unadded.  This is a sentinel-persistence failure, not a failed
factorisation check.

PID 21364 and its wrapper ended naturally.  No project build, judge, oracle, or
Colab process owned by this campaign remained when `TOKEN LIBRE` was reported.
