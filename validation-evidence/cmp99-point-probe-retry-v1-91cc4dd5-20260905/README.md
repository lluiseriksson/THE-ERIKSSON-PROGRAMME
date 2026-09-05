# Physical point-probe retry v1 — diagnostic PASS, not production seal

Source: 91cc4dd5d6133e0eb0fc59279d58a71487caa6c7.
Colab CPU/high RAM50.99GB/no GPU, host8f59de7fdfaa.
Start2026-09-05T14:21:22.908259+00:00; launcherPID1199.
Lean4.29.0-rc6; Mathlib07642720480157414db592fa85b626dafb71355b.
No project-build restoration; nevertheless cold_seal=false by draft contract.

## Immutable evidence

Outer point-probe-retry-v1-preservation-20260905.tar.gz (123412 bytes):
fb98e86845e56187eb26f834958c572d6ff8d0165db40d10560cfde9ef471cd4.
Inner hrpoly-cmp99-point-probe-retry-v1-evidence.tar.gz (104343 bytes):
21dc287d46f7fbef95c043a443e835d7805f32469d77691af405044c2a391a73.
Both downloaded with a separate download-only cell, verified against Colab
hashes, copied here. The calculation cell was not reexecuted.

Pinned verifier388892e5b8ac817d3143958dcd5c0cd0eec00600:
verify_cmp99_point_probe_retry.py SHA256
49fe9095784b34cebd6a06f47170a9cb02bb675bbfc947cada1d3c3e9fad28.
Helpers, launcher, raw logs, transport and recorded exits remain in the outer
archive and its extracted directory. The inner archive is authoritative.

## Verification

LAUNCH_FINAL_STATUS=PASS; launcher exit0. Child physical_diagnostic exit0,
2243.349851095s; archive_verifier exit0,0.210912593s.
Independent Windows read-only verifier: PASS,18 stages,2 public axioms,
2 actual output hashes;0.2948062s, observed peak23789568bytes, one Python
process, no Lean/Lake. Exact invocation:

```text
C:\Python312\python.exe <this-directory>/point-probe-retry-v1-launch/verify_cmp99_point_probe_retry.py --helpers <this-directory>/point-probe-retry-v1-launch --archive <this-directory>/hrpoly-cmp99-point-probe-retry-v1-evidence.tar.gz --sha256 21dc287d46f7fbef95c043a443e835d7805f32469d77691af405044c2a391a73
```

| Stage | Exit | Seconds |
|---|---:|---:|
| Mathlib point-probe repro | 0 | 3.821374250 |
| Physical prerequisites | 0 | 2075.680366480 |
| Physical point-probe draft | 0 | 10.919515549 |
| Final source-clean gate | 0 | 1.263041785 |

Exact accepted public names, each with {propext,Classical.choice,Quot.sound}:

- YangMills.RG.cmp99ComplexOuter_singleFinitePiLp_eq_pointSource_draft
- YangMills.RG.cmp99PhysicalStep7b_complexSingle_eq_pointSource_draft

Actual SourceFlowPhysicalPointProbeDraft.olean:
48f4646e39b4897b742b0b938f4bbfeae3b841c61c8b3af57353d083d74cc24f.
Actual SourceFlowPointProbeRepro.olean:
6443ee37e9821c02a2ad46357a2aa9b8f7d1590e8a5a76ad7bbf1ecb056efb1f.
Dependency linter warnings are retained; no whole-graph warning-free claim.

## Cleanup and scope

At15:08:52UTC launcherPID1199, lean and lake process checks were empty.
Runtime disconnected/deleted about15:09UTC (~48min connected); reconnect
state verified. Monitor deleted and final disconnected browser tab closed.

The whole Lie-vector input identity is proved under the canonical complex
embedding and exact physical carrier permutation. No outer-norm isometry,
regional inverse, derivative B0, or window15 attainment follows.
No promoted PRE-VALIDATION marks retired.20/41,TermSource0 unchanged.
