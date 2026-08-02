# INC-SPATIAL-DUAL-BOND-LEAN-001 — runtime correction and corrupted Lean archive

Date: 2026-08-01

Campaign: task 14, exact local dual-bond identity

Lean source SHA under test: `85847dd19623c692b8345cee864be7837f5c7656`

Preregistered runner SHA: `d41fa43a78370bf93cdc181a9f8d9d0d89ba080b`

## VERIFIED FAILURE

The first Colab allocation was a standard CPU runtime with 2 logical CPUs and
`13286936 kB` total RAM.  The symbolic gate passed in normal and optimised
Python, but the run was deliberately interrupted during the official Mathlib
cache download before any Lean build.  The runtime was not the high-memory
plane required by the campaign, so its interrupted output is not evidence.

The notebook was then restarted on the requested high-memory CPU runtime:
Linux `6.6.122+`, 8 Intel Xeon logical CPUs, `53467192 kB` total RAM, Python
`3.12.13`, and no GPU.  The immutable repository SHA, toolchain file, Mathlib
pin, symbolic-gate SHA-256, and both normal/`-O` symbolic gate runs all passed.

Toolchain installation failed closed before cache retrieval or elaboration:

```text
$ elan toolchain install leanprover/lean4:v4.29.0-rc6
info: downloading https://releases.lean-lang.org/lean4/v4.29.0-rc6/lean-4.29.0-rc6-linux.tar.zst
info: installing .../leanprover--lean4---v4.29.0-rc6
error: failed to extract package
info: caused by: Unknown frame descriptor
[exit 1]
RuntimeError: command failed (1): elan toolchain install leanprover/lean4:v4.29.0-rc6
```

The module build, full core build, permanent oracle, consistency judge, job
counter, artifact construction, and final PASS cell did not run.  Therefore
this incident says nothing about whether `SpatialDualBond.lean` elaborates.

## Diagnosis and next action

The failure occurred while extracting the downloaded Lean archive, before the
repository source entered the elaborator.  The next attempt will use a fresh
high-memory ephemeral session and the same immutable notebook and source SHA.
If the archive failure repeats, the runner rather than the theorem must be
repaired and preregistered in a new commit before another execution.
