# Physical reflection cold promotion — PASS preserved locally

2026-09-07: cold focal PASS (8653 jobs, exit 0, 1209.894459 s),
audit PASS (exit 0, 30.804162 s), 52 exact declarations, 17 materialized outputs.
Independent local reader accepted the downloaded archive and all 14 stages.
Local preservation: `validation-evidence/neumann-physical-reflection-promoted-cold-v1-20260907/`.
Outer SHA-256: `b246caedbaceb018e9b16efbd9f76ed1c6cd509f6fe1154a19281246ae27a3c5`.
Inner SHA-256: `7c6512cd94dfc8311bc2874487c12ae0eab7b9ce18e580a1cc531b51bba86081`.
Independent report: `local-independent-verification.txt` in that directory.
Selective production-header/ledger sealing is recorded in Addendum 1197; no
proof bodies changed. Counters remain unchanged.

Retained-runtime bounded orbit diagnostic launched once, PID 62369, from pinned
runner ec751f5dcd834d921a898c82c96fc835bfcaa010; its log is
`/content/neumann-boundary-orbit-hot-v1-launch.log`. It is NOT a cold seal.
Diagnostic FAIL: missing BalabanCMP89NeumannReflectionOrbitAlgebra.olean,
before proof elaboration (exit1, 0.867197 s). Archive SHA-256
`cc8f71ceb3a61d9c2a27fa606039e097b64779ae9d9df55bac18b025f80c6cf5`
is durable in validation-evidence/neumann-boundary-orbit-hot-v1-20260907.
Runtime disconnected/deleted approximately 03:56 UTC after both packages
were preserved. Do not rerun the old notebook or either launcher. Next action:
prepare an explicit prerequisite stage for the bounded orbit retry.

Retry prepared at source108f30f9 (same Lean blob); runner checkpoint3f9e88f70,
scripts/colab_neumann_boundary_orbit_diagnostic.py, blob SHA-256
6b26d11c8d28080e5c993545b05a84c5feeb9f0bf2b62aee6bd4f57341c1b858.
New fresh diagnostic directory /content/hrpoly-neumann-boundary-orbit-diagnostic-v2.
Queue: explicit ReflectionOrbitAlgebra build, unchanged orbit repro (120 s),
clean-source check. This is NOT a production seal and does not recompile the
physical reflection prefix. It has not been launched.
Independent reader scripts/verify_neumann_boundary_orbit_diagnostic.py has a
synthetic PASS fixture and five rejected corruptions (including missing
prerequisite stage, nonzero exit and sorryAx with consistent log hashes).
Measured local test: 0.224071 s, 19529728 bytes observed RSS; no compiler used.
Prepare the pinned Colab launch and read its independent verdict next.

The launch instructions below are historical records, not active processes.

Source checkpoint: `84ceb5f2f466ab8f4e9dea175fd412c7bf63a21e`.
Runner/verifier checkpoint: `acdc7db315eb00690296c4fe1d55f3deda4f81cb`.
Launcher checkpoint: `eb879bdd2ebfffe427ad6f20fff57c9d4e396f69` (published).
Branch: `codex/cmp116-interacting-wilson-hessian`.

Seventeen production modules plus one audit. Bodies checked against diagnostic
checkpoint `0e652a6b170cd109163afbd5362134b8ce658d37`: 17/17 exact after only
import-path relocation and extraction of print-axiom lines; 52 unique audited
declarations. All eighteen textual guards passed. Local check 0.587372 s,
15376384 bytes observed RSS. Reader self-test: eight corruptions rejected,
0.1174609 s, 18341888 bytes observed RSS. These checks are not compiler evidence.

Colab tab 23, runtime f33828f71ae2, CPU/high RAM, lluiseriksson@gmail.com.
Single launch at 2026-09-07T03:25:33.709004+00:00, parent PID 48754.
No original notebook cell rerun. Fresh checkout directory:
`/content/hrpoly-neumann-physical-reflection-promoted-cold-v1`.
No project `.lake/build` restored from the retained diagnostic checkout.

Read-only continuation commands in the Colab terminal:

```sh
ps -p 48754 -o pid,stat,etime,args
tail -20 /content/launch-physical-reflection-cold-v1.log
tail -20 /content/neumann-physical-reflection-promoted-cold-v1-launch/physical_cold_graph.log
```

Do not restart on an observer timeout. The launcher preserves the child exit,
checks the cold archive independently and emits final status. Output archive:
`/content/neumann-physical-reflection-promoted-cold-v1-preservation-20260907.tar.gz`.
After completion download/preserve and independently verify hashes before
selective removal of production PRE-VALIDATION. Preserve first error on FAIL.
All earlier HOT/FAIL archives are durable in validation-evidence.

This is an intermediate cold brick, not terminal hRpoly. Regional image-series
equation and mixed-boundary seam remain open, along with the full-lattice
operator dictionary. Counters remain 20/41, TermSource=0, window15 not attained.
Unrelated dirty worktree files have not been touched.
