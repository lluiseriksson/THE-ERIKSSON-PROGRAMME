# INC-SPATIAL-SYMWEIGHTED-GATE-004

Date: 2026-08-01

## Intended certification campaign

Certify the preregistered symWeighted factorisation gate in normal and
optimised Python using a fresh detached run directory, persistent per-mode
logs, real child exit codes captured after `WaitForExit`, and atomic completion
sentinels.

The judge remained fixed at raw commit
`06226edc9221fa60a6ed39e30ae84c848bd66041`, SHA-256
`a95e66da0ee527b1776ceb3d13d83760d1fd88cc9227ebea668a2b98ca1946cf`.

## Normal-mode unit

The detached wrapper was PID 30840 and its Python child PID 16532.  The child
started at `2026-08-01T11:06:26.6096162+02:00`.  Polling used three 40-second
windows followed by a final bounded check.  The output file was completed at
`11:09:36+02:00`; the child was observed absent by `11:09:40+02:00`.

`normal.stdout.log` contains valid PASS JSON with all required counts:

- 5460 configuration pairs checked;
- 5460 scale mutations rejected;
- 5460 source closing-bond omissions rejected;
- 5460 target closing-bond omissions rejected.

The 294-byte stdout SHA-256 is
`08e597a81abee7535a0124589a506a239e6317e4b2f0c6729cf51342c1d5d4af`.
Stderr was empty, SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## Instrumental failure

The wrapper captured the child exit code in memory after `WaitForExit`, but
failed while building metadata because `Get-FileHash` was unavailable inside
that detached PowerShell environment.  It therefore never wrote a final
sentinel.  The wrapper failure log SHA-256 is
`22c1d49bdb31b093feffab05931f8b6d1e1acfdd479d0cad2a42bbdb522a0b29`.

Under the mandatory reader semantics, an absent sentinel is not completion.
There is no persisted exit code, no certified normal run, and no permission to
start optimised mode.  `python -O` was not launched.  This is a wrapper
capability failure, not a failed factorisation check.

## Prepared repair, not executed

`scripts/run_spatial_symweighted_gate_detached.ps1` replaces `Get-FileHash`
with .NET SHA-256 and codifies the required protocol.  Each mode has distinct
semantic names (`normal` or `optimized`).  Its final `<mode>.exitcode` contains
exactly one decimal line, written first to `<mode>.exitcode.tmp`, closed,
checked for positive length and integer parse, then renamed atomically.
Metadata is separate.  Existing per-mode files are refused.

The repair was prepared but not executed in this campaign.  At the checkpoint
both PIDs had ended naturally, no heavy process owned by Task 14 remained, and
the token was reported free.

Static validation was also non-executing.  Its first supervisor command had a
PowerShell typo (`in$required`) and failed before parsing the target file.  The
corrected invocation parsed the wrapper with zero syntax errors and confirmed
the required protocol tokens.  No `normal` or `optimized` child was launched by
either validation command.
