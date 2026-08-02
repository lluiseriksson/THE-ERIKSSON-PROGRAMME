# Spatial-ring Colab metadata probe failure 001

Status: **VERIFIED failure**. This is neither a certified Lean result nor evidence about the spatial-ring bound.

## Scope

- Campaign: canonical task (14), uniform spatial-ring bound.
- Branch: `codex/spatial-ring-uniformity`.
- Lean interface target: `5da2453fb24b09be544983f698661d3917119061`.
- Notebook preregistration: `1b556c59da8acd737c32a04897c4e9c036a770f3`.
- UTC start reported by the notebook: `2026-07-31T20:29:58.066752+00:00`.

## Runtime observed before failure

- Google Colab authenticated runtime, CPU with high RAM selected.
- Kernel: Linux `6.6.122+`.
- CPU: 8 logical CPUs, Intel Xeon at 2.20 GHz.
- RAM: `53467192 kB` reported by `/proc/meminfo`.
- Python: `3.12.13`.
- GPU: none exposed to the runtime.

## Failed gate

The preregistered metadata cell called:

```text
nvidia-smi --query-gpu=name,memory.total,driver_version --format=csv,noheader
```

The command was marked optional, but Python raised before a process result existed:

```text
FileNotFoundError: [Errno 2] No such file or directory: 'nvidia-smi'
```

The exception originated in `subprocess.run` inside the notebook's `run` helper. Consequently the notebook stopped before cloning the repository, installing Lean, obtaining the isolated mathlib cache, or elaborating any declaration. No PASS was emitted and no mathematical output was produced.

## Diagnosis and bounded correction

The helper handled nonzero exit codes but not a missing optional executable. The correction is limited to translating `FileNotFoundError` into exit code 127 when, and only when, `allow_failure=True`. Required commands continue to fail closed. The exact repository SHA, Lean toolchain pin, mathlib pin, judges, and proof source remain unchanged for the rerun.
