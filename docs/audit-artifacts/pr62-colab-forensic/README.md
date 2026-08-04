# PR #62 forensic Colab evidence

This directory preserves the four complete raw command logs requested after
the limited external audit of draft PR #62.  It is provenance evidence only;
it is not a mathematical review and does not replace that audit.

## Frozen object and method

- Previous PR HEAD: `254687f52993aad70191c014bace1184a11487b5`
- Mathematical checkout: `36a02972d0f6771acb2f9594b6306cc08db39faf`
- Branch cloned: `codex/testigo-agudo-n2-q`
- Runtime: Google Colab Pro+ CPU/high-RAM, accelerator `none`
- Measured CPU: `AMD EPYC 7B12`
- Measured memory: `53467192` KiB
- GPU checks: `nvidia-smi` absent and `torch.cuda.is_available() = False`
- Lean toolchain: `leanprover/lean4:v4.29.0-rc6`
- UTC interval: `2026-08-04T23:00:39.021495+00:00` through
  `2026-08-04T23:38:18.614625+00:00`

The notebook and full runner were written while disconnected.  After choosing
CPU and high RAM in the Colab UI, the runner installed `elan`, made a fresh
filtered clone, checked out the mathematical SHA in detached-HEAD state, and
verified an empty `git status --porcelain=v1`.  For each command it opened the
named log in binary mode, merged stderr into stdout, wrote every subprocess
chunk to disk before echoing it to the notebook, waited for the subprocess,
and only then computed the byte count, line-ending counts, exit status, and
SHA-256.  Thus the files below are the raw command streams, not text copied
from the browser output.

## Preserved raw logs

| Command | Raw log | Exit | Bytes | LF | CR | SHA-256 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| `lake exe cache get` | `phase0_frozen_cache.log` | 0 | 10,173 | 49 | 88 | `36a184938168b7d019c5df0ea9cdedd29fc4dcd193ae5f29aa6e3d9f550a388a` |
| `lake build YangMills.OS.SpatialSharpWitness` | `phase0_frozen_module.log` | 0 | 2,106 | 42 | 0 | `5544e5406d132928c735108062c3227435fda135697ffd66650594dd9e1f844f` |
| `lake build YangMillsCore` | `phase0_frozen_core.log` | 0 | 106,497 | 1,643 | 0 | `67cc3646acf800c809d8e116d9c1c0c8652a7700b0487cef4d898d39d002817f` |
| `lake env lean oracle_check.lean` | `phase0_frozen_oracle.log` | 0 | 346,431 | 5,189 | 0 | `8dc4dfaa790d0d42155ac2ef9d1410a2dc2d47f78af512cc94b4f1a0f0a00188` |

The module and Core logs end in successful `8172 jobs` and `8469 jobs`
summaries respectively.  The oracle log is byte-identical to the digest
recorded in the original manufacture transcript.  Cache progress and build
timings are environment-dependent, so the other three newly preserved logs
have new hashes; their commands and exit statuses are the frozen ones.

`manifest.json` and `transcript.txt` were generated inside Colab after all
four subprocesses exited.  `setup-transcript.txt` records the independent
runtime and checkout checks.  `SHA256SUMS` covers those three records and all
four raw logs.

## Download and independent verification

Colab produced `/content/pr62-forensic-evidence.zip`:

- bytes: `44,156`
- SHA-256: `e11022dcee1a77637f6ab41aa03877c6905f6cc8158b47e33b4969bc1d0f6593`

The ZIP was downloaded through the Colab browser and hashed on Windows before
extraction.  Every entry named by `SHA256SUMS` was then independently hashed
again and matched.  No Lean, Lake, or oracle command ran on Windows.
