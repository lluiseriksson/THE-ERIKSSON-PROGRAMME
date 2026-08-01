# Spatial odd-orbit-fold Lean witness interruption 001

Date: 2026-08-01

Status: **instrumental failure**.  No Lean certificate is claimed.

## Immutable inputs

- Notebook object: repository commit
  `5bf542ba39c6b2bac981f375c3c4aaf07f164120`.
- Theorem/source checkout:
  `fca2f37705bc06cf659829bde64ea0fd5c810638`.
- Judge SHA-256:
  `43d218195d497f65d8e6012081a36215a363574fbf3046dccc3eec01eb18ab89`.
- Lean `v4.29.0-rc6`, commit
  `00659f8e6071d7e46131ed643bf8003b99b044e9`.
- Mathlib `07642720480157414db592fa85b626dafb71355b`.
- Fresh CPU-only Colab root
  `/tmp/spatial-odd-orbit-fold-dnsearsx`; no GPU or second campaign shared the
  runtime.

The notebook checked all repository, judge, toolchain, Lean-commit, and
Mathlib pins before running the gate or Lean.

## Completed units

The preregistered rational gate returned exit 0 in both normal Python and
`python -O`.  Their JSON payloads agreed exactly and checked ring sizes 1
through 7, 254 action rows, 10922 paired summands, and rejection of 10922 sign
mutations, 10922 omission mutations, and 10920 head-only-flip mutations.

`lake build YangMills.OS.SpatialRing` returned exit 0 with 8171 jobs.  The new
`YangMills.OS.act_flipOdd_eq_sum_zero_head` theorem compiled on its first Lean
attempt.  `lake build YangMillsCore` then returned exit 0 with 8466 jobs.

## Interruption

The next command was:

```text
lake env lean /tmp/spatial-odd-orbit-fold-dnsearsx/repo/oracle_check.lean
```

After roughly 37 minutes in that command, and 1 h 53 min of visible cell time,
the cell ceased running without an exit code.  The only platform-state text
visible in the UI was the literal Swedish string `Ansluter`.  Waiting another
40-second polling slice left the same literal state.  No rejection message,
traceback, Lean error, oracle output, consistency result, PASS marker, or ZIP
artifact was produced.  No cause such as resource exhaustion or excess
sessions is inferred.

The runtime was explicitly disconnected and deleted.  The UI then displayed
`Återanslut`, and the browser tab was closed.

This is a failure of the execution witness, not evidence for or against the
theorem or its axiom set.  In particular, the successful module/core builds do
not certify the permanent oracle.

## Recovery contract

Recovery uses the same immutable preregistered notebook object and theorem SHA
in two fresh, independent CPU Colab runtimes.  Neither may reuse this root or
its outputs.  Both must complete the normal/optimized gate, module build, core
build, permanent oracle, consistency judge, PASS marker, and artifact
download.  The deterministic gate payload and permanent-oracle output hashes
must agree across the two completed witnesses before certification.

Even a successful recovery certifies only the exact finite-sum orbit-fold
identity.  It proves no odd-sector norm bound, no even non-Perron bound, and no
part of the uniform spatial-ring `specRatio` inequality.
