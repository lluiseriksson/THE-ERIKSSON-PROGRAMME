# C1 paper changelog

## v1 (commit 814b9f2, 2026-07-11)
Initial draft: three endpoints stated, certified table inked from the
committed transcript only, measured registration failure recorded
(rem:crossover), non-vacuity section, two slots live.

## v2 (commit e6cc0b1)
Third-desk (Codex) audit round 1 applied. Numbers PASS (7+ significant
digits, all rows and crossovers; script sha independently reproduced).
One overclaim sustained and fixed: eps* = 1/Lambda is no longer called
a "certified activity radius for the endpoints" — the endpoints prove
coefficient bounds M·Lambda^n; the activity-series passage is
paper-level algebra conditional on the eps^n structure, and the paper
says so. Band booleans re-scoped to the two registered endpoints with
the exact monotonicity extension noted; strict-gate wording.

## v3 (commit bae1f5f)
Catalan promotion after the measured pin-drift audit
(KP/RootedLeafSummation blob identical to UPSTREAM.lock; the
Appendix-F file drifted +144/−15 additively, carrying the treeShape
refactor and the already-merged Catalan route). The exact identity
n!·C_n and the sharpened marked-root bound M^{2n+1}·C_n rise from
cited remark to endpoints of the paper (5 endpoints). Provenance
records the drift audit.

## v4 (commit 802cea92)
Editorial closure round against the external 7.10/10 review:
- NEW readable-definitions section (rho as Steiner length, S#/T# as
  tree-graph majorants, with the signed-coefficient passage
  explicitly scoped upstream).
- NEW proof-architecture section (Catalan bijection with n=2 worked
  example; one-pin sums / moment-paid-once / 2n+1 budget; target
  preservation).
- NEW quantitative section (exact ratios 4^n/C_n through n=30;
  polynomial-only honesty; truncation reading at certified rows).
- NEW related-work section — all 10 references verified online this
  session with journal/volume/pages and DOI/arXiv where they exist.
- NEW reproducibility section: theorem-to-artifact map,
  clean-clone command sequence, pin-drift audit, toolchain pins.
- NEW conclusion with explicit limitations.
- Transcript reproduced from scratch (byte-identical, exit 0) and
  recorded in the certified section.
- Overfull boxes reduced to four sub-8pt instances.

## v5 (this release)
- Lean integration committed on green build; oracle output for the
  five endpoints and two non-vacuity theorems inserted verbatim
  (slot closed).
- Release commit, tag, and build facts recorded in Reproducibility.
- Five-role independent audit round (formal, numeric, mathematical,
  hostile-editorial, reproducibility) logged in docs/C1-CHARTER.md
  with resolutions.
