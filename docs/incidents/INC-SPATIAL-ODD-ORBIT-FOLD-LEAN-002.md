# Spatial odd-orbit-fold Lean recovery cache failure 002

Date: 2026-08-01

Status: **VERIFIED infrastructure failure**.  Lean was not run.

## Immutable inputs and isolation

Recovery-B opened the preregistered notebook object at repository commit
`5bf542ba39c6b2bac981f375c3c4aaf07f164120` in a fresh, independent Colab
high-RAM CPU runtime.  The runtime reported Linux `6.6.122+`, Python `3.12.13`,
eight Intel Xeon logical CPUs at 2.20 GHz, 53467192 kB RAM, no GPU, UTC start
`2026-08-01T14:55:50.531879+00:00`, and root
`/tmp/spatial-odd-orbit-fold-6yqq9g0n`.

The clone checked out source SHA
`fca2f37705bc06cf659829bde64ea0fd5c810638`.  Repository, toolchain, Mathlib,
and judge-hash prechecks passed.  Normal Python and `python -O` both returned
the exact expected gate payload with exit 0.

## First error

The isolated official-cache command was:

```text
lake exe cache get
```

It returned exit 1 with the literal terminal line:

```text
uncaught exception: no such file or directory (error code: 2) file: /root/.cache/mathlib/9b7efb42d099baec.ltar.part and/or /root/.cache/mathlib/9b7efb42d099baec.ltar
```

The notebook raised `RuntimeError: command failed (1): lake exe cache get` and
stopped.  No module build, core build, oracle, consistency judge, PASS marker,
or artifact ZIP ran.  No cause is inferred from the missing temporary/cache
file.  In particular, this is not evidence for or against the Lean theorem.

The runtime was immediately disconnected and deleted.  The UI confirmed
`Återanslut Mycket RAM-minne`, and the tab was closed.  Recovery-A was a
different Colab runtime with a different root and remained active; it shared
neither filesystem nor outputs with this failed unit.

## Recovery contract

This runtime supplies no terminal witness.  A replacement must start from the
same immutable notebook in another fresh independent high-RAM CPU runtime and
complete every preregistered stage.  The already-running Recovery-A is not a
replacement for the missing second complete witness.
