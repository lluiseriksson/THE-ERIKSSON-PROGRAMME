# FULL flag: first failure preserved, HOT v2 active

Same Colab tab55, runtime opened 2026-09-07 10:27:07.753886 UTC.
Original PID10827 completed FAIL before project build: minimal repro
unknown identifier Nat.cast_mul at line12; childexit1/2.404496429s.
Archive SHA256 f8c60493a0e56bd0b614bce099cdb88b01f6fa8ac27c7a89182bc63304ed420e
downloaded by assistant and preserved under
validation-evidence/neumann-full-flag-diagnostic-v1-failure-20260907/.
Local failure check exit0/0.0970269s, observed peak RSS10174464 bytes.

Bounded HOT v2 PID18097 is active on the retained runtime. Only overlay
change: Nat.cast_mul -> Int.natCast_mul in both draft/repro, written as
tmp/NeumannFullFlagCastReproV2.lean and tmp/NeumannPhysicalFullFlagDraftV2.lean.
Original Git files unchanged. Source base f0c58431d20042ced9177632409e9f9bcbe79692.
Repro exit0/18.367807325s with exact axiom propext, verified by named gate.
Next stage is building NeumannRectangleDirectionalMasks, then five-name
physical draft audit. No physical result or seal yet.

Read ONLY /content/neumann-full-flag-hot-v2/launch.log from Cell2.
Do not execute Cell1 or repeat the HOT launcher. HOT runner and overlays are
under /content/neumann-full-flag-hot-v2, future archive is that path+.tar.gz.
Final JSON contains actual child exits/times/log hashes, source-overlay
hashes and exact audits. Preserve and independently check on completion;
bounded repair on first error if needed. No Windows Lean/Lake or CI.
20/41, TermSource=0 and window15 open unchanged.
