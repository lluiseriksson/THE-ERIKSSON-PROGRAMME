# Eq. (3.59) real-slice gate: high-RAM preflight rejection

This package preserves the fail-closed preflight result from the first retry
after the preceding runtime loss.

- source checkpoint: `08039bcbc4bc74af072bef0252d7d559cbc80fe5`
- runner revision: `eq359-real-slice-promoted-cold-v3`
- runtime opened: `2026-08-26T15:57:06.848553Z`
- measured runtime: CPU, `12.67` GiB RAM
- result: `HIGH_RAM_REQUIRED`, before checkout or Lean/Lake execution
- runner-reported evidence JSON SHA-256:
  `AA9F20E34E00DFF0FCA54D8B015F0A81F8EF1D93F9738B036C7439391AB8783A`
- downloaded archive SHA-256:
  `A7F166D998660D41A14D3475103627EBB175CFE1CE9C20A1787F3791EE747590`

Classification: **BLOCKED-RUNTIME-PREFLIGHT**.  This is not a mathematical
FAIL and certifies no source module.  It does not authorize removal of
PRE-VALIDATION.  Counters remain `20/41`, `TermSource = 0`; window 15 remains
compatible but unattained.
