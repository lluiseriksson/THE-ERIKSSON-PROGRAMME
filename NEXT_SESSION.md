# NEXT_SESSION.md — Top-level orientation

**For**: any agent or human picking up the project after the 2026-04-25 Cowork session
**Last updated**: 2026-04-26 (Phase 484, post-435-phase session — past saturation threshold per OBSERVABILITY §7.6; see `SESSION_BOOKEND.md` "Post-bookend overflow note" for honest framing of late phases)

> **Note**: A separate `YangMills/ClayCore/NEXT_SESSION.md` exists scoped to F3 work. This document orients agents who arrive at the project root without a specific F3 context.

---

## 0. Where we are right now (60 seconds)

The 2026-04-25 Cowork session ran 398 phases (49-446) and produced:

- **38 long-cycle Lean blocks** (`L7_Multiscale` through `L44_LargeNLimit`).
- **17 Mathlib-PR-ready files** (`mathlib_pr_drafts/*_PR.lean`, Phases 403-420).
- **Triple-view structural characterisation of pure Yang-Mills** via three complementary physics-anchoring blocks:
  - **L42** (Phases 427-431, 5 files): **continuous view** — asymptotic freedom, RG running, dimensional transmutation, mass gap, area-law confinement. See Finding 021.
  - **L43** (Phases 437-439, 3 files): **discrete view** — Z_N center symmetry, Polyakov loop as order parameter. See Finding 022.
  - **L44** (Phases 443-445, 3 files): **asymptotic view** — 't Hooft coupling λ = g²·N_c, planar dominance, reduced N_c-independent β-function. See Finding 023.
- **Surface-doc propagation complete**: every relevant top-level doc carries post-Phase 410 + 432 + 440 + 446 addenda.
- **Cross-reference audit done**: `MATHLIB_GAPS.md` and `MATHLIB_PRS_OVERVIEW.md` now cite each other explicitly.
- **Submission playbook done**: `MATHLIB_SUBMISSION_PLAYBOOK.md` is the operational guide for landing 9-10 PRs upstream.
- **2 sorry-catches** in the physics-anchoring arc: Phase 437 (L43, ω ≠ 1 hypothesis) and Phase 444 (L44, asymptotic → uniform bound).

**Project status**:

- 0 sorries (maintained throughout the session).
- 0 axioms outside `Experimental/` (unchanged).
- ~12% Clay literal incondicional pre-attack programme → **~32%** post-Phase 402 (after the 12-obligation creative attack programme).
- 17 PR-ready files queued for Mathlib upstream (none built with `lake build`).

---

## 1. Pick a direction (the four options)

In rough order of decreasing tractability:

### Option A — Land Mathlib PRs upstream

**Effort**: 10-13 hours focused work.
**Prereq**: a Mathlib build environment with `lake`.
**Outcome**: 9-10 merged Mathlib PRs.
**Read first**: `MATHLIB_SUBMISSION_PLAYBOOK.md` (operational), `mathlib_pr_drafts/INDEX.md` (priority queue).

This is the **highest-value-per-hour** direction available right now. The 17 files are math sketches with Lean drafts; in a real build environment, each takes ~30-45 min of polishing. After 9-10 PRs land, the project's outward Mathlib contribution is recorded.

**Step 1**: read `MATHLIB_SUBMISSION_PLAYBOOK.md` §1 and §2.1.

**Step 2**: start with `MatrixExp_DetTrace_DimOne_PR.lean` (closes literal Mathlib TODO).

### Option B — Build verification of the 35 Lean blocks

**Effort**: medium (depends on whether the project's build is clean).
**Prereq**: project clone + `lake`.
**Outcome**: confirmation that the 35 Lean blocks (~310 files, ~37200 LOC) actually type-check.

The session produced ~340 Lean files **without running `lake build` locally**. The Codex daemon may have been validating in parallel, but no end-to-end confirmation was recorded.

**Step 1**: `cd <project clone> && lake build YangMills.L41_AttackProgramme_FinalCapstone.AttackProgramme_GrandStatement` (deepest leaf).

**Step 2**: if any block fails, file an issue at the relevant block location. The blocks are numbered L7-L41; earlier blocks are foundational, later ones consume them.

### Option C — Substantive Yang-Mills work

**Effort**: large (each is multi-day).
**Prereq**: Yang-Mills math background.
**Outcome**: incremental movement on `Clay literal incondicional`.

Per `FINAL_HANDOFF.md` post-Phase 402 addendum, the next substantive directions are:

1. **Concrete `WightmanQFTPackage` instantiation** with placeholder `Unit` fields replaced by actual Wightman data (requires significant Mathlib infrastructure).
2. **Upgrade individual attacks** from "abstract derivable" (current state) to "Yang-Mills concrete with constants from first principles" (requires Mathlib gauge theory infrastructure not yet available).
3. **Continue the `BalabanRG/` push** with Codex daemon (the 222-file infrastructure landed mid-session is structurally complete but has open analytic obligations).
4. **Derive the L42 anchor constants `c_Y` (= `m_gap / Λ_QCD`) and `c_σ` (= `σ / Λ_QCD²`) from first principles** (Finding 021): currently both are accepted as anchor inputs in `L42_LatticeQCDAnchors`. Deriving them is essentially the substance of solving the Clay Millennium problem itself for SU(N).

Each of these is a multi-day project requiring deep Mathlib + math input. They are not "next session" tasks; they are "next month" tasks.

### Option D — F3 closure (pre-existing front)

**Effort**: medium.
**Prereq**: F3 chain understanding.
**Outcome**: closes the standing F3-Count and F3-Mayer obligations.

Read `YangMills/ClayCore/NEXT_SESSION.md` for the F3-scoped roadmap. This was the active front before the 2026-04-25 session pivoted to creative attacks + Mathlib PRs. It remains live.

---

## 2. Don't do these

- **Do not** add another long-cycle Lean block (L42+) before reading `BLOQUE4_LEAN_REALIZATION.md` to understand what's already covered. The 35 blocks are dense; adding more without orientation produces overlap.
- **Do not** add another PR-ready file without first attempting to land at least one of the existing 17 upstream. The current 17-file collection is at saturation; adding #18 before any merges happen is low-value.
- **Do not** trust the % Clay literal incondicional bar without reading the honesty caveats in `README.md` §2 and `FINAL_HANDOFF.md` post-Phase 402 addendum. The ~32% number includes "abstract derivable" attacks that haven't yet been concrete-instantiated.
- **Do not** modify `YangMills/ClayCore/` files without `#print axioms` discipline. The core is held to `[propext, Classical.choice, Quot.sound]` only.

---

## 3. Read order for orientation

If you have **5 minutes**: read `FINAL_HANDOFF.md` (the 60-second TL;DR doc with all post-session addenda).

If you have **15 minutes**: add `STATE_OF_THE_PROJECT.md` (current snapshot) and `COWORK_FINDINGS.md` Findings 001-020 (the strategic narrative).

If you have **30 minutes**: add `BLOQUE4_LEAN_REALIZATION.md` (35-block master narrative), `mathlib_pr_drafts/INDEX.md` (PR queue), `MATHLIB_PRS_OVERVIEW.md` (outward catalog).

If you have **60+ minutes**: add `MATHLIB_SUBMISSION_PLAYBOOK.md` (operational PR playbook), `OPENING_TREE.md` (master strategy from Phase 1), `CLAY_CONVERGENCE_MAP.md` (cross-branch convergence).

---

## 4. Honest caveats to repeat in any external description

The full caveat list is in `README.md` §2-§3 and `KNOWN_ISSUES.md`. Briefly:

- `ClayYangMillsMassGap 1` (N_c = 1) is the trivial group SU(1), not abelian QED-like U(1). The bound holds vacuously. (Finding 003.)
- `ClayYangMillsPhysicalStrong` for N_c ≥ 2 has hypotheses that remain not-fully-discharged. (Finding 004.)
- The project does **not** claim to solve the Clay Millennium theorem. It targets the lattice mass gap, which is one input toward but distinct from the Clay statement. (`MID_TERM_STATUS_REPORT.md` §6.3.)
- The 17 PR-ready files **have not been built with `lake build`**. They are math sketches + Lean drafts, not verified contributions. (`MATHLIB_PRS_OVERVIEW.md` §5-§6.)
- The ~32% Clay literal incondicional figure is post-attack-programme; pre-attack baseline was ~12%.
- The 35 Lean blocks include 12 attack-programme blocks that close obligations at the **abstract derivable** level, not at the **concrete-with-derived-constants** level.

---

## 5. If you only have 1 hour and want to make a tangible difference

Open `MATHLIB_SUBMISSION_PLAYBOOK.md` §2 and try to land **one** PR upstream.

Recommended single-hour target: `LogTwoLowerBound_PR.lean` (smallest, simplest, ~30 min polish).

A merged Mathlib PR is a tangible outward contribution that survives the project's eventual fate. The project itself is one path among many toward the Clay Millennium statement; a merged Mathlib PR is permanent infrastructure that benefits the formalised math community regardless.

---

*Cross-references*: `FINAL_HANDOFF.md`, `STATE_OF_THE_PROJECT.md`, `COWORK_FINDINGS.md`, `MATHLIB_SUBMISSION_PLAYBOOK.md`, `mathlib_pr_drafts/INDEX.md`, `BLOQUE4_LEAN_REALIZATION.md`.
