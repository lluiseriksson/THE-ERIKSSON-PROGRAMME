# INC-SPATIAL-SYMWEIGHTED-GATE-002

Date: 2026-08-01

## Intended campaign

Measure the preregistered symbolic judge
`scripts/judge_spatial_symweighted_factorization.py` locally during an
exclusive Windows window, first in normal Python and only then in optimised
Python.  The gate source remained the immutable raw commit
`06226edc9221fa60a6ed39e30ae84c848bd66041`, SHA-256
`a95e66da0ee527b1776ceb3d13d83760d1fd88cc9227ebea668a2b98ca1946cf`.

## Resource preflight

The first preflight found a foreign
`lake build YangMills.RG.BalabanCMP98Eq123QuadraticFrontier` and aborted before
starting Python.  A bounded monitor observed the foreign process disappear
after 36.3 seconds.  Only then was the normal-mode judge started.  No Lean,
Lake, oracle, or Colab process was launched by this campaign.

## Observed infrastructure failure

The normal-mode judge ran as PID 19520, command

`C:\Python312\python.exe scripts/judge_spatial_symweighted_factorization.py`.

It started at `2026-08-01 10:34:49+02:00`.  The external measurement harness,
which was sampling wall time and RSS without deciding the verdict, reached its
124-second command limit before the judge returned.  The harness ended but did
not terminate PID 19520.  The orphaned atomic judge was monitored without
interference until it exited by itself at `2026-08-01T10:37:40+02:00`, about
171 seconds after creation.

Because the parent stdout pipe had already disappeared, no judge JSON, exit
code, PASS, or reliable peak-RSS measurement was recovered.  Optimised mode was
not started after the global single-build-token instruction arrived.  The
cause of the inconclusive record was the 124-second harness limit, which was
shorter than the judge's approximately 171-second runtime.  This incident is
not evidence of a defect, timeout, or failed assertion inside the judge: its
verdict was never captured.

## Consequence

This run is inconclusive solely as a measurement record, not a gate PASS.  It
demonstrates that the current exact SymPy formulation is not a negligible
desktop check: normal mode alone survived beyond two minutes.  It says nothing
negative about the factorisation or the judge.  The one proposed Lean theorem
remains unfabricated.  A later campaign must run the unchanged judge with a
detached log and durable exit-code sentinel, or preregister a separately
justified, cheaper exact gate before execution.

At the safe checkpoint no matching project Lean/Lake process and no
`judge_spatial_symweighted_factorization.py` process owned by this campaign
remained.  The build token was reported free for Task 22.
