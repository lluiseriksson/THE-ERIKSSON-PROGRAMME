# Spatial odd-orbit-fold Recovery-A interruption 003

Date: 2026-08-01

Status: **instrumental failure**.  The module build returned no exit code.

## Intended witness

Recovery-A opened the immutable preregistered notebook object
`5bf542ba39c6b2bac981f375c3c4aaf07f164120` in a fresh Colab high-RAM CPU
runtime.  The UI reported 50.99 GB RAM and no GPU.  This runtime was distinct
from Recovery-B and shared no filesystem or outputs with it.

The notebook reached the command

```text
lake build YangMills.OS.SpatialRing
```

so its clone, source/toolchain/Mathlib/judge prechecks, normal and optimized
rational gates, Lean installation, and isolated official-cache stage had all
completed without a recorded failure.

## Interruption

During the module build the cell ceased running without printing build output
or an exit code.  The only final platform-state text visible was the literal
`Återanslut Mycket RAM-minne`.  No rejection message, traceback, Lean error,
module job count, core build, oracle, consistency result, PASS marker, or ZIP
artifact was produced.  The runtime root and exact UTC stop time were not
durably captured before the platform disconnected, so this record does not
invent them or assign a cause.

The already-disconnected tab was closed.  This runtime supplies no Lean
witness and no evidence for or against the theorem.

## Recovery contract

The next recovery is a single isolated high-RAM CPU session from the same
immutable notebook, with no concurrent Task 14 runtime.  It must complete all
preregistered stages and download a validated artifact.  A second wholly fresh
complete witness remains necessary afterwards for terminal reproducibility.
