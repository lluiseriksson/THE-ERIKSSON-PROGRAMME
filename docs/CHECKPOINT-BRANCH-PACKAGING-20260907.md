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

## Current result — cold gate PASS and runtime released

### Next source now written (not compiled)

`tmp/NeumannMixedOwnerDraft.lean` at `bab8c90d09f7dfeaf7965ce3b0381a96bfabd19e`;
SHA256 `4d37d5ae52d3b8b3323e6b460b145b0a655ea829acc8afee09387a9a24fc8621`.
Seven audit declarations cover packaged-image equality, owner transport,
common-source injectivity, owner equality iff, and unchanged counting indicator.
It imports only the now-sealed packaging and integer owner algebra. Exact
overlay text guard passes; compiler result is NOT CHECKED. No runtime opened.
Prepare one bounded Colab diagnostic: pinned fresh checkout/toolchain/cache,
build the sealed `YangMills.RG.NeumannMixedBranchPackaging` prerequisite,
then run `lake env lean tmp/NeumannMixedOwnerDraft.lean` with exact seven-name
audit and real exit code. Preserve first failure and use a minimal repro for
any pure Mathlib elaboration error before retrying. This draft is not a cold
production seal and must not change counters. The theorem coefficient stays
literal; physical carrier classification and inverse equations remain outside.

Ledger1220: focal3290jobs exit0/56.254445132s; audit7names exit0/4.768029778s.
Independent reader verifies16 stages. Durable archive
`validation-evidence/neumann-mixed-branch-packaging-cold-v1-20260907/neumann-mixed-branch-packaging-cold-v1.tar.gz`,
SHA256 `b1f33671a8ac555162b88469f4f92a90e69ca3035af137668eb91ab929d9b310`.
Runtime824 terminal, evidence preserved, unassigned; Reconnect observed by
09:46:39UTC, all tabs closed. No runtime remains retained. No HOT was appended.
Next: prepare same-index owner dictionary M2 against the now-sealed packaging,
then use Colab for a bounded diagnostic. No request for new authority needed.

### Preserved launch metadata (not a live process)

Published notebook checkpoint `ef8e762132a7c0ff69b97e9d2be5976595518e3f`:
`scripts/colab_neumann_mixed_branch_packaging_promoted_cold.ipynb`.
Runner/reader checkpoint `579882fb91f11022f39003c9f6af2f53d339af13`.
Runner SHA256 `9cf22262126e325c186559f033f7a1c4d96f8365e949d8cf5e9ad89b673856fd`;
reader SHA256 `f8034619436e99d5c1f78010d03fffe6300d69b3d52e66fef09cb646ec03f90b`.
Opened2026-09-07T09:40:04.019789UTC, CPU50.99GiB, parentPID824.
Hash/preflight passed; subsequently PASS as recorded above.
Historical browser tab51 is closed. Never reexecute the old Cell1.
Cell2 reads `/content/mixed-branch-packaging-promoted-cold-launch-v1/launch.log`
and its pid.txt. Check the same process; an observer timeout is not a failure.
On completion preserve archive, independently verify, then cold-seal only
the exact two production headers if PASS. A bounded next HOT must be prepared
before retaining the runtime; otherwise preserve and disconnect immediately.

Reader synthetic test passed1positive/8negative; exact axiom parser2positive/9negative.
Overlay checks passed on exactly2 files. One local guard invocation used a
string instead of Path and failed before checking source; corrected invocation
passed. This was local instrumentation only, not a Lean failure.

## Cold contract

Prepared by specializing the existing
`colab_neumann_mixed_fixed_source_promoted_cold.py` contract to
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
That previous runtime is closed; the new gate above is now the sole active
session. No Lean/Lake ran in Windows; local checks stayed below30s/512MiB.
No CI dispatched. GitHub last verified as lluiseriksson before fast-forward.
Unrelated worktree changes were not staged.

Counters remain20/41; TermSource0; window15 open. Goal remains active.
