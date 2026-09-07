# Continuation checkpoint — 2026-09-07

Branch: `codex/cmp116-interacting-wilson-hessian`.
Source prepared for the next cold gate:
`c9818c183643a19b0cb88d614ea7b10ad3e8eda6`.

## Preserved results

- Mixed fixed-source cold seal: `6a41633e7`, ledger1217. Exact source
  `8da9ffc57d7de329501fc5ba5d8084cdcbe5fb4f`, three declarations,16 stages verified.
- Branch-packaging HOT first failure retained in ledger1218; no false seal.
- Branch-packaging HOT-v2 PASS, ledger1219; seven declarations plus isolated
  Mathlib repro. Source `476cc52e0b672438a2e6e23d21e2769c2db9cdef`.
- Production promotion contains the identical HOT theorem bodies, checked
  against Git blobs with explicit UTF-8 decoding. PRE-VALIDATION remains.

## Next bounded operation

Prepare the cold runner/independent reader/notebook by specializing the
existing `colab_neumann_mixed_fixed_source_promoted_cold.py` contract to
`YangMills.RG.NeumannMixedBranchPackaging` and its Audit. Do not claim a
cold result from the HOT archive. Exact source hashes:

- `YangMills/RG/NeumannMixedBranchPackaging.lean`:
  `59e3a9b65ce551d3f1fc2c3d8f50c036bf6901c19d0f974ba0792ca72ca91377`.
- `YangMills/RG/NeumannMixedBranchPackagingAudit.lean`:
  `8d052d9770051ad58cdaa04effc9bc7ae90bc959567a68d907d999b0729998d8`.

Queue: `lake build YangMills.RG.NeumannMixedBranchPackaging`, then
`lake env lean YangMills/RG/NeumannMixedBranchPackagingAudit.lean`.
Colab only; fresh checkout, no project build cache restoration, exact pins,
stop-on-first-error. Verify runner/reader instrumentation before connecting.

After that, owner transport must use the SAME global mixed index. FULL
classification still needs the literal physical carrier; the current Bool
is algebraic data, not a discharged physical identification. No inverse or
uniform B0 claim follows from the at-most16 branch count.

## Resource and evidence state

Runtime opened09:14:40.226806UTC CPU50.99GiB. ParentPID5144, HOT-v1PID15123,
HOT-v2PID16356 all terminal before unassign. All three archives downloaded
and independently hashed locally before release. Colab showed Reconnect
at09:34:49UTC; exact printed closure timestamp was cleared by unassignment
and is not claimed. All browser tabs closed; no Colab process retained.
No Lean/Lake ran in Windows; local checks stayed below30s/512MiB.
No CI dispatched. GitHub last verified as lluiseriksson before fast-forward.
Unrelated worktree changes were not staged.

Counters remain20/41; TermSource0; window15 open. Goal remains active.
