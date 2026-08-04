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

## v5 (commit eae151ca)
Five-role audit round applied: hostile editor (25 findings, 5
blocking: false submitted-to-Mathlib claim, tricotomy breaches
including the title, unwitnessed reproduction claim, omitted u >= 0
hypothesis, reserved-word collisions), mathematical referee (6
discrepancies: swapped gate-factor attribution in the architecture,
example wording, corollary provenance, L >= 3 neighbor count,
superadditivity gloss), numeric auditor (PASS, zero findings, third
independent library). Reproduction witness committed
(scripts/c1_admissibility_rerun_20260711*).

## v6 = c1-v1.0 (release)
- Lean integration committed on green build (commit 4f95a5ad,
  8244 jobs, exit 0): module MarkedRootedClosure with the five paper
  theorems, the non-vacuity witnesses (structured proofs after two
  measured `decide` failures, diagnosis in the commit message), the
  oracle file, and archive/UPSTREAM.lock.
- Axiom oracle clean on all seven theorems —
  [propext, Classical.choice, Quot.sound] — log committed as
  scripts/c1_oracle_output.txt.
- Final slot closed with the recorded release facts; date line
  cleared; tag c1-v1.0.

## v6.1 = c1-v1.0.1 (documentation patch; tag c1-v1.0 never moves)
External review of the tag (8.55/10, "apto para preprint") sustained
three archival gaps, all patched here with ORIGINAL artifacts only:
- Raw build logs of all three runs committed (they existed in the
  session scratchpad; the repo's `*.log` gitignore rule had silently
  excluded them — renamed to .txt, content untouched).
- Dual-hash witness v2: the v1 reproduction witness recorded the
  CRLF-worktree SHA (0319...); the canonical LF-blob SHA (46C6...)
  is now declared alongside it, both re-derived and matching the
  reviewer's own computation.
- RELEASE-MANIFEST.md: integration commit / manuscript commit / tag
  / canonical blob hashes in one table; charter Amendments 4-5
  (release registry + PASS 7/7 audit) now inside the patch tag.

## Known remaining limitations (explicit)
- The signed-coefficient-to-majorant passage is upstream
  (machine-checked there); the activity-series algebra is paper-level
  and stated as such.
- The Catalan gain is polynomial; no convergence radius moves.
- The non-vacuity witness certifies satisfiability, not sharpness.
- The full clean-clone Lean rebuild was executed once this session
  (cold cache, ~8244 jobs); the reproducibility command sequence is
  committed but a second from-scratch external replay has not been
  run on other hardware.
- The PlaneTree Mathlib PR is prepared but not yet opened.

## v6.2 (author-name correction)
Author name corrected to "Lluis Eriksson" (no accent) at the owner's
instruction - the diacritic was lost with the move to Sweden and the
legal/administrative name is unaccented.  Content otherwise
untouched; the v6.1 blob hashes in RELEASE-MANIFEST.md remain
correct as scoped (they are tag-scoped to c1-v1.0.1/.2).

## v6.3 (self-citation correction - MATERIAL)
The Catalan identity was publicly announced by the author on
2026-07-02 as ai.viXra.org:2607.0001 (the companion repository's own
README cites it); the related-work claim 'we are not aware of a
published statement in exactly this form' was therefore false by the
author's own record.  Corrected: the preprint is now cited
([Eriksson26]), the novelty claim is scoped to INDEPENDENT prior
sources, and the paper states explicitly that it subsumes the
announcement into the hole-respecting toolkit.  Found by the owner
cross-checking his viXra author page; the fabricating desk had read
that repository during reconnaissance and missed the README pointer
- recorded as this arc's miss.
