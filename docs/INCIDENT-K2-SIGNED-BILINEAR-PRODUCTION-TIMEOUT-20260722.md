# Incident: signed-bilinear K2 candidate production timeout

**Date:** 2026-07-22  
**Status:** `DESIGN_TIMEOUT`; no K2/G2 promotion

The current-tree rerun of
`scripts/run_surface_remainder_signed_bilinear_production.py` was given the
registered grid 48 and the full 158 endpoint `t` births.  It reached 133
strict-positive rows before the 300-second operational ceiling terminated the
process.  No terminal verdict, manifest, or independent replay was emitted.

The observed rows are not evidence of a complete cover: the missing rows and
the required exact transcript/manifest/replay remain unresolved.  The partial
transcript was removed from the worktree so it cannot be mistaken for an
authoritative artifact.  The earlier complete design campaign remains
explicitly design-only.  A future run must use a resumable production driver
whose final artifact is written atomically only after all 158 rows and the
independent structural validator pass.
