# Machine-verification audit — 2026-07-31

## Frozen checkout

- Audit branch base: `origin/main` at
  `f65e969cc165185e96184c0a16f362079ef2bd9e`.
- Census commit on the audit branch:
  `9556c4315a20a21532cd9a099d7e733e47d59412`.
- `lake-manifest.json` SHA-256:
  `e2f2d45a5fef5ae352e6f8be858726d603d83fde30d740a14a8a2a588579381d`.
- `lakefile.lean` SHA-256:
  `09d3ff29b030a20c396cdd5f729230eeb7bcde3ae91cda519c0643ac6b715bd5`.
- `YangMillsCore.lean` SHA-256:
  `0bb911d659b63c92de1871801915550f9d8db0508ccd73ec6a583a0df9c392e7`.
- The Lake file pins mathlib to
  `07642720480157414db592fa85b626dafb71355b` and names
  `lake build YangMillsCore` as the sound-core target.

## Build status

`lake build YangMillsCore` was launched from this worktree. The controlling tool
call reached its 1,804-second limit while the process was still compiling pinned
mathlib dependencies. The child `lake`/`lean` process continued after the launcher
timed out and is monitored separately. Until the process terminates with exit code
0 and a terminal transcript is captured, the result is **INCONCLUSIVE / NOT A
PASS**. No manuscript's printed job count or PASS banner is substituted for that
terminal result.

## Sorry and project-axiom scan

A source scan of tracked project `.lean` files, excluding `.lake`, temporary and
output trees, found no active line beginning with `sorry`. It found 15 active
project `axiom` declarations, all under `YangMills/Experimental/**`:

- five in the experimental semigroup/Bakry--Emery lane;
- ten in the experimental Lie-SU(N) lane.

Three additional text matches beginning with the English word “axiom” occur
inside module comments and are not declarations. `YangMillsCore.lean` has no
`import YangMills.Experimental...` line, but import-closure and `#print axioms`
claims are not upgraded until the target build and the intended oracle command
complete successfully.

Raw local scans are retained under:

- `tmp/publication-audit/lean-active-sorry-axiom-scan.txt`;
- `tmp/publication-audit/lean-sorry-axiom-scan.txt`;
- `tmp/publication-audit/lean-source-scan.txt`.

## Per-paper replay boundary

Many public PDFs report Lean commits, job totals or Python suites but do not bind
all of the following in one independently recoverable instruction: immutable
checkout, executable target, exact inputs, oracle list and expected transcript.
Those claims remain **author-reported machine-certified** in the ledger. The
middle-batch attempt to locate the suite cited by `2602.0088v3` failed because the
paper-named path is absent from this checkout. That absence is an audit finding,
not a failed theorem and not a PASS.

Python replacement-package verifiers are run both normally and with `python -O`.
They contain no `assert` statements; their O0/O1 transcripts are separate. A
passing package verifier establishes only its explicit integrity, rendering and
finite counterexample checks, not an unstated mathematical theorem.
