# F4 uniform scalar amplitude: promoted graph, PRE-VALIDATION

The draft diagnostic at source
`be4e73409ac444d23e95c2eae2584fece5882f98` passed; its durable evidence
is recorded in ledger Addendum 1115. This is not the cold seal of the
following promoted graph.

The finite queue is:

1. `BalabanCMP85FullGreenNormalizedBudget` and Audit (2 declarations).
2. `BalabanCMP85SourceFullGreenHybridAmplitude` and Audit (1 declaration).
3. `BalabanCMP85SourceFullGreenUniformAmplitude` and Audit (5 declarations).

All six files are under `YangMills/RG/`. They remain outside the root
aggregator and retain PRE-VALIDATION. No source/audit is already sealed.
The pure power repro is diagnostic scaffolding, not a production dependency.

Promotion changes only the three module paths, the normalization namespace,
the explicitly renamed local Draft/_draft declarations, module-header
provenance, and relocation of eight public axiom prints to separate audits.
A static comparison of all three mathematical texts under those explicit
renamings matched. This is not a substitute for Lean elaboration.
In particular, no imported `cmp89..._draft` API is silently renamed.

## Acceptance

Fresh Colab CPU/high-RAM checkout at the exact promoted source SHA;
verified Lean 4.29.0-rc6 asset and Mathlib
`07642720480157414db592fa85b626dafb71355b`.
No restoration of project `.lake/build`; focal and audits may share
that single fresh checkout. Stop on the first real child failure.
Require all eight expected public audit declarations and only the allowed
axioms. Preserve source/runner hashes, child exits, timings, raw logs,
archive/report hashes, and verify the downloaded bytes before retirement.

The endpoint chooses positive rho,C before all depths j for fixed a>0 and
L>=2, with four simultaneous strip conditions and the literal source-flow
full owner amplitude bounded by C times R^-2, R=L^(j+1).
Do not replace R^-2 by one. This is neither a regional inverse
identification nor a derivative estimate. F5's physical-spacing and
regional-inverse gates remain independent, visible work.

Until this separate cold gate passes: no PRE-VALIDATION retirement,
root-build claim, physical B0 claim, window-15 attainment or terminal
counter movement. Counters remain 20/41 and TermSource=0.

## Prepared cold runner

Source checkpoint: `5138e9bd4bc88797c91c21df5bb5c630c71600ca`.
`scripts/colab_cmp85_uniform_full_green_promoted_cold.py` fixes that
source SHA and six SHA-256 values obtained from binary `git cat-file blob`,
not worktree text. Its six-stage queue alternates each focal and its audit.
The existing pinned durable runner and exact axiom parser are reused.

`scripts/verify_cmp85_uniform_full_green_promoted_cold.py` independently
checks source, toolchain, Mathlib, source blobs, archive membership, queue,
child commands/exits/times, raw-log hashes and all eight public axiom blocks.
The read-only synthetic self-test passed (six rejected corrupted fixtures,
plus the underlying parser's two accepted/nine rejected fixtures). This is
instrument validation only, not Lean evidence. The launcher must run it
before the cold queue. Python AST parsing of both new scripts also passed.
