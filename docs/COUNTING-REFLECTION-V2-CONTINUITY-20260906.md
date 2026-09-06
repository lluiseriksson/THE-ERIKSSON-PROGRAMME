# Counting reflection v2 — diagnostic running, not a seal

This is a continuation checkpoint, not a mathematical verdict. Counters remain
20/41, TermSource=0, window15 compatible but not attained.

## Immutable inputs and single launch

- Source: `06a928178b22c42c4ecc5387461b808ee3a19dea`.
- Runner commit: `a336b6fa972c16e3f282e96ee0327da90c5d665b`.
- Runner SHA256: `4f985fdb7e65c32dee72a71e81e85b1f2d8a97553ca9758bc34934679d862b5d`.
- Notebook commit: `ae6d6bd7b6d4ea5f401bc489d9a1f53869c8534f`.
- Notebook path: `scripts/colab_neumann_generated_counting_reflection_diagnostic_v2.ipynb`.
- Revision: `neumann-generated-counting-reflection-diagnostic-v2`.
- Colab account visibly verified: `lluiseriksson@gmail.com`.
- CPU, high RAM, no GPU; actual reported RAM 50.99028778076172 GiB.
- Hash-gated execution began `2026-09-06T05:41:39.700843+00:00`.
- Host `3e1d8ed2110d`; child PID `8252`; exactly one code-cell execution.
- Latest initial observation: toolchain/dependency cache preparation succeeded;
  `geometry_leaf` executing. No final status observed at this checkpoint.

The original v1 FAIL is preserved in ledger1127 and
`validation-evidence/neumann-counting-reflection-diagnostic-fail-20260906`.
The old host was lost only after that archive was downloaded and verified.
The prepared HOT retry was never executed on the replacement empty host.
This fresh diagnostic is necessitated by measured runtime loss, not by a
decision to discard a usable warm checkout.

## Evidence verification prepared before completion

`scripts/verify_neumann_counting_reflection_diagnostic_v2.py` pins this source,
runner, revision, both Lean blobs, exact commands, outputs and axiom names.
It preserves the original v1 verifier unchanged. Synthetic checks reject
12 bad evidence cases plus five malformed launcher serializations; the
pinned axiom parser also rejects nine forbidden/malformed cases.
Passing fixtures are instrument tests, never compiler evidence.

Measured self-test: exit0, 0.1323491s, 17223680 observed peak bytes.
The first local codec self-test rejected an overescaped suffix at exit1;
that instrumentation error was corrected before any real verdict was read.

The committed notebook emits one literal backslash-n after the launcher JSON.
The v2 verifier explicitly decodes exactly that suffix, or ordinary JSON
whitespace, with duplicate keys/nonfinite constants/extra content rejected.
Original bytes remain hashed and preserved. This is not stdout verdict parsing
and does not alter the notebook cell while it runs.

`scripts/preserve_neumann_counting_reflection_diagnostic_v2.py` invokes the
independent verifier before writing anything, refuses an existing destination,
rechecks the archive hash, and preserves both nested archives and reports.
It remains unexercised on a real v2 PASS until such an artifact exists.

## Continue without repeating the cell

Keep the single Colab tab/runtime. Read only the current stage/process;
do not reexecute, reload, or infer success from a completed prefix.

Remote log:
`/content/neumann-generated-counting-reflection-diagnostic-v2-launch/diagnostic.log`.

Remote evidence:
`/content/hrpoly-neumann-generated-counting-reflection-diagnostic-v2-evidence/evidence.json`.

Expected preservation archive:
`/content/neumann-generated-counting-reflection-diagnostic-v2-preservation-20260906.tar.gz`.

On completion, preserve/hash the exact archive first. PASS needs all four queue
stages, all five named axiom blocks, exact source blobs and both output hashes.
FAIL retains the first nonzero child and its exact log, with no prefix promoted.
Retained runtime may be reused only for the bounded repair/promotion preparation;
disconnect after evidence and scoped work are safe, not before retrieval.

The next mathematical boundary is unchanged: full-carrier counting-mass probe
reflection is not the arbitrary-rectangle retained Neumann inverse. R1/R2/R3/R4
in `docs/F5-REGIONAL-INVERSE-ACCEPTANCE-GATES.md` remain the acceptance map.
