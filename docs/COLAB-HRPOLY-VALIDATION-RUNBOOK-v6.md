# Colab hRpoly validation runbook — official toolchain bootstrap v7

This is validation infrastructure, not a mathematical checkpoint.  Windows is
used only for Git and lightweight hash checks.  Lean, Lake and oracle commands
run only in a new Colab Pro+ CPU/high-RAM runtime with no GPU.

## Immutable roles

- `SOURCE_CHECKPOINT_A` contains
  exactly the 27 source paths derived from overlay v4.  Eight module headers
  add the mandatory `PRE-VALIDATION` warning; theorem statements, constants
  and hypotheses are unchanged.  A is the only source object compiled.
- The driver checkpoint is a descendant of A.  Its A-to-driver source-neutral
  diff contains exactly this document and `scripts/colab_hrpoly_validation_v6.py`.
- Base before A: `072b0955a1ee524fefa0826da4d34a432e69e6df`.
- Source A: `1f86b3c4ff9ebf52ac8b6f4ca7f22aa3b5cc92ad`.
- Repository: `https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git`.
- Toolchain: `leanprover/lean4:v4.29.0-rc6`, official Linux x86_64 asset
  `lean-4.29.0-rc6-linux.tar.zst`, SHA-256
  `bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e`.
- Mathlib: `07642720480157414db592fa85b626dafb71355b`.

The runner contains the 27 path/SHA-256 pairs.  It rejects any difference
between the base-to-A path set and that manifest, any changed byte, any dirty
source checkout, any unexpected A-to-driver path, or a driver for which A is
not an ancestor.

V7 supersedes v6's assumption that `lake` is preinstalled, manual
`files.upload()` and all `drive.mount` runbooks for this
campaign.  It does not supersede their retained failure evidence.  It uses no
tags, Drive, interactive upload or credentials.  It downloads the official
Lean release by fixed URL and digest, may install the ephemeral `zstd` utility,
and never changes the mathematical source checkpoint.

## Open and bootstrap exactly once

1. Open a new Colab Pro+ runtime: CPU, high RAM, no GPU.  Record UTC opening
   time.  Do not leave it idle.
2. Substitute the published full B SHA below.  Execute this cell exactly once:

```python
from pathlib import Path
import subprocess

REPO = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
DRIVER_CHECKPOINT = "<PUBLISHED_FULL_SHA_DRIVER>"
DRIVER = Path("/content/hrpoly-driver")

assert not DRIVER.exists()
subprocess.run(["git", "clone", "--no-tags", REPO, str(DRIVER)], check=True)
subprocess.run(
    ["git", "-C", str(DRIVER), "checkout", "--detach", DRIVER_CHECKPOINT],
    check=True,
)
subprocess.run(
    [
        "python3",
        str(DRIVER / "scripts/colab_hrpoly_validation_v6.py"),
        "--driver-root",
        str(DRIVER),
        "--driver-checkpoint",
        DRIVER_CHECKPOINT,
        "--repo-url",
        REPO,
    ],
    check=False,
)
```

Do not re-run the cell after a disconnect or UI stall.  Inspect visible output
and `/content/HRPOLY_V7_QUEUE_STARTED`.  The runner's exclusive sentinel makes
a second queue start fail before heavy work.

The runner performs, in order:

1. Driver HEAD, A-as-ancestor, and A-to-driver transport-only diff gate.
2. Portable timing preflight (`true` returns 0, `exit 23` returns 23) and four
   sentinel states: absent, exclusive creation, identity match, duplicate
   rejection.
3. Download and SHA-256 verification of the official Lean 4.29.0-rc6 asset;
   ephemeral `zstd` installation when needed; extraction; `lean --version`,
   `lake --version`, and executable hashes recorded.
4. Two independent fresh HTTPS clones, `/content/hrpoly-source-a` and
   `/content/hrpoly-source-b`, each detached at A.
5. Exact 27-file path and SHA-256 gate, toolchain gate, clean-tree gate.
6. Independent dependency/cache materialization in each clone.  A failed
   official cache fetch is recorded and falls back to source compilation;
   `lean-toolchain`, `lake-manifest.json`, and Mathlib's exact SHA are gated.
7. The stop-on-first-error queue in each clone:
   `RestrictedVisitedTransferPowers`; Mathlib pin; OptimalInteractionAlpha and
   audit; CombinedKernelSupport and audit; CombinedHessianSupport and audit;
   CombinedTerminalEq143 and audit; partial TermSource constructor and audit;
   `YangMillsCore`; full `oracle_check.lean`.
8. Audit parsing: every printed axiom set must be a subset of
   `{propext, Classical.choice, Quot.sound}` and every audit must emit at least
   one `#print axioms` result.
9. Equality of the two deterministic semantic-result SHA-256 hashes.  Raw
   logs and their own hashes are retained separately and are not hidden by the
   normalized comparison.

The two source clones may share only the verified toolchain.  They do not share
`.lake`, build outputs, logs or working state.

## Evidence download and shutdown

At green completion or first error the runner prints:

- `FINAL_STATUS`
- `EVIDENCE_ARCHIVE`
- `EVIDENCE_BYTES`
- `EVIDENCE_SHA256`
- `CONNECTED_RUN_SECONDS`

It creates the archive under `/content`.  In a second, evidence-only cell call
`google.colab.files.download(<printed archive path>)` once.  If browser download
fails, retain the full visible stdout and report the literal error; do not
repeat the builds.  Verify the downloaded SHA-256 on Windows using a
lightweight hash command.  Publication after that is transport only and does
not determine the mathematical verdict.

Immediately disconnect and delete the runtime after the download attempt or
the first error.  `CombinedTerminalEq143`, its audit and the constructor remain
unverified unless both fresh source clones reach and pass them.
