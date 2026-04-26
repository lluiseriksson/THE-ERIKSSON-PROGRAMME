# `mathlib_pr_drafts/` — README

**One-line summary**: 17 PR-ready Lean files for upstream Mathlib submission, plus older F3-related drafts. None has been built with `lake build`.

## What's in this folder

- **17 PR-ready files** (Phases 403-420 of session 2026-04-25): elementary `Real.exp` / `Real.log` / hyperbolic / numerical / matrix lemmas missing from Mathlib in packaged form. See `INDEX.md` for the full organisational doc with submission ordering.
- **3 older drafts** (Phases 8, 22, 38, January-March 2026): `AnimalCount.lean`, `PiDisjointFactorisation.lean`, `PartitionLatticeMobius.lean`. These pre-date the current 17-file collection. `KlarnerBFSBound_PR.lean` (in the 17-file set) supersedes `AnimalCount.lean` with a cleaner statement.
- **PR description docs**: `PR_DESCRIPTION.md`, `PR_DESCRIPTION_Gap2.md`, `PR_DESCRIPTION_Gap3.md` for the older drafts.
- **Reference scaffold**: `F3_Count_Witness_Sketch.lean` (NOT for PR — internal reference only).

## Where to start

| If you want… | Read |
|---|---|
| The submission roadmap | `INDEX.md` (this folder) |
| The outward-facing catalog | `../MATHLIB_PRS_OVERVIEW.md` (project root) |
| The findings log entry | `../COWORK_FINDINGS.md` Finding 020 |
| The 60-second TL;DR for the project | `../FINAL_HANDOFF.md` post-Phase 410 addendum |
| The complementary "what we need from Mathlib" doc | `../MATHLIB_GAPS.md` |

## Critical caveat

**No file is ready for upstream PR submission as-is.** Each file was produced inside a Cowork session **without access to a Mathlib build environment** (no `lake`). Tactic-name drift (`pow_le_pow_left`, `lt_div_iff₀`, `Real.log_inv`, `Real.exp_nat_mul`, etc.) is real and will require non-trivial polishing per file.

**Path to merged Mathlib PR**: clone Mathlib master → drop file in → `lake build` → fix tactic-name drift → run `#lint` → open PR.

Each individual proof is 2-5 lines; expect ~30 min per file of polishing in a real build environment.

See `INDEX.md` §4 (per-file pre-PR checklist) and §6 (honest meta-caveat) for full details.

## Naming conventions

Files in this folder follow the pattern `<HeadlineTheoremName>_PR.lean` so they are visually distinguishable from non-PR files. Each one contains:

- Apache-2.0 copyright header (matches Mathlib).
- Module docstring with proof strategy + PR submission notes.
- Main theorem(s) with detailed `/-- ... -/` docstrings.
- `#print axioms <theorem_name>` at end of each block to verify no spurious axiom slipped in.

---

*Last updated: 2026-04-25 (Phase 423). Maintained by the Cowork agent (Claude) under supervision of Lluis Eriksson.*
