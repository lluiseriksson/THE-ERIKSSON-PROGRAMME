# Counting reflection v2 — verified diagnostic PASS, not a seal

The v2 diagnostic and independent preservation passed. This is not a cold production seal. Counters remain
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
- Final status PASS, total 1541.415481849s. Prerequisites8486 jobs exit0 in
  1368.899147928s; draft exit0 in10.627043463s; all five named axiom blocks
  (two repro plus three draft) have exactly the permitted trio.

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
It passed on the actual downloaded v2 archive: exit0,0.2614003s,
19189760 observed peak bytes under the30s/512MiB watchdog.
Outer SHA256 `ed2cda8e2fac4c51a1d49b140b5956fd0ba05134b9e0f2dddf4c1fecfa522d92`;
inner SHA256 `a204cb56197db16a315a9f5432b65f31b5e595ad454e7a1686be933c85cf7df7`.
Durable directory `validation-evidence/neumann-counting-reflection-diagnostic-v2-20260906`.
Preservation record SHA256 `4b25845fafdbc8162c92af893fb1b6fdbf9befe68b4cce98bece4043a6996d41`.

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

## Next bounded HOT candidate prepared while v2 runs

Source `214b6923f3523d44282d5772fa6ab09782864f10` adds the independent
`tmp/NeumannRetainedCountingMassDictionaryDraft.lean`; binary Git-blob SHA256
`6f8a5be71b33261c263291b9049337ed068f1aee282f7eb1482b264bcd91e7f6` (5144 bytes).
Its production `YangMills` tree is exactly the v2 base tree
`d60f95120f11de18d0d3e3a73e90c9b59db07f05`; source/pin diff is empty.
Text/import guards: exit0, 0.2184146s, 18907136 observed peak bytes.

`scripts/colab_neumann_retained_counting_dictionary_hot.py` was launched once
after the actual v2 archive was independently verified and preserved locally.
Its runner commit is `dd6d8b17a233d84bb82da47efef1a51d1721ff0a`, binary blob
SHA256 `483774c10b45d38de8fc40a79709207f1b73ea0dd26d765e2aa8db216d7c6538`.
Remote launch log: `/content/neumann-retained-counting-dictionary-hot-v1-launch.log`.
No verdict is claimed for this new HOT run yet. It requires the actual preserved v2 archive digest as
`--prior-sha256`, invokes the pinned independent v2 verifier before any Lean,
rejects an already running Lean/Lake process, checks base/source tree/Mathlib,
and refuses reused work/input directories. It then materializes only the two
needed import targets and compiles the one draft, with real child exit codes,
timeouts and exact two-name axiom gate. No checkout mutation or cold seal.
AST/pin/order checks: exit0, 0.2059736s, 17215488 observed peak bytes.

Do not run this candidate after a v2 FAIL: preserve and repair the first error
instead. Do not infer the prior digest from a filename or substitute a v1
archive. Retrieve and verify v2 before continuing in its retained runtime.

The separate HOT verifier `scripts/verify_neumann_retained_counting_dictionary_hot.py`
revalidates the real prior archive, exact input/runner blobs, stage commands,
exit codes, logs, output and both named axiom blocks. AST and a real unrelated
archive rejection passed (0.4224512s,21139456 observed peak bytes); it has not
yet been exercised against an actual HOT PASS. Instrument tests are not Lean evidence.
