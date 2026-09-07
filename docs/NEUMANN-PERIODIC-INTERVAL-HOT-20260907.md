# Bounded periodic interval diagnostic — prepared, not executed

Draft source: e7bfd29f609408eccd6f296c1f96e04425320d8c.
Runner: 4d3f72c5a2d26843cf8b5d86639be597f6a7b744,
scripts/colab_neumann_periodic_interval_hot.py.
Git-blob SHA256: c003e2ce10f40d3861fb96d9feeac22e39383adbeb1922ca396ba9160259841e.

Do not execute before the currently running periodic-series cold archive is
downloaded, independently verified and durably preserved. Its source is
d16030e70abeee9eb77e28f5dc6a222ffdfd8200; the HOT runner verifies that exact
parent again, as well as the unchanged retained checkout. It cannot turn a
HOT result into a cold seal.

Use the retained high-RAM Colab runtime only after the cold process exits.
Invoke the hash-verified runner once with `--parent-sha256` equal to the
observed, locally verified cold archive digest. No checkout changes, no
project source edits and no second compiler process alongside the cold gate.

Queue: parent reader; HEAD; clean-before; Mathlib-only repro (60 seconds);
sealed interval prerequisite (900 seconds); exact six-name draft/audit
(120 seconds); clean-after. Every stage records its real child exit code;
first error stops the queue. The repro substitutes only the exact interval
type definition and imports; the proof bodies remain the downloaded draft.

Preserve `/content/neumann-periodic-interval-hot-v1.tar.gz` and verify with
scripts/verify_neumann_periodic_interval_hot.py using the cold parent archive,
both actual archive hashes and pinned helpers. No promotion follows from HOT
alone. Disconnect/delete the runtime after evidence is preserved.

Reader synthetic tests: one accepted fixture, eleven rejected fixtures,
including stale source, cold-label upgrade, modified repro, forbidden axiom,
unexpected archive members and corrupt output. Measured local test exit0,
0.3284593 seconds, 19,820,544 bytes observed peak RSS; no local compiler.

This tests the FULL-coordinate part of mixed M1/M2, not the complete mixed
equivalence, physical point-source equation, regional inverse or uniform B0.
Counters remain20/41, TermSource0, window15 not attained; Clay untouched.
