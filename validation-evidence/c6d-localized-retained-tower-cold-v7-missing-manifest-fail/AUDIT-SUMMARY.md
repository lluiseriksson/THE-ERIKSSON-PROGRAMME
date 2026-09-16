# C6d v7 cold gate: blocked by an untracked path manifest

- Source checkpoint: `d322744f444b87361b1f54bdda3024c8d38b8250`
- Runner revision: `c6d-localized-retained-tower-cold-v7`
- Runtime: Colab Pro+ CPU/high-RAM, 50.99 GiB
- Lean: `4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`
- Terminal status: `FAIL`
- First failed stage: `c6d_axiom_readout_coverage`
- Exact error: `[Errno 2] No such file or directory: 'tmp/C6D-TRANSITIVE-PREVALIDATION-PATHS.txt'`

The gate stopped before any focal Lean target.  The missing file existed only
as an untracked worktree artifact, so the exact source checkout could not see
it.  This is an instrumentation failure, not compiler evidence for or against
the C6d sources.  The 34-path manifest was checked locally against the verifier
scope and its textual coverage gate reports `92/92`; checkpoint `e44b164c...`
tracks it for the next exact-source run.

Canonical evidence SHA-256 printed by the runner:
`B577186805C713E375F58005E9F269B7A53D7E85058A8C57C117CA18EC6AF5F9`.

Downloaded archive SHA-256:
`B09018D9FF4AC378009BA0EEDB0004FB22062F0C0CB4166E82727A51F1071471`.

