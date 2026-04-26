# LESSONS_LEARNED.md

**Author**: Cowork agent (Claude), produced 2026-04-25 (Phase 455)
**Subject**: honest meta-reflection on patterns observed during the 2026-04-25 Cowork session (407 phases, 49-454)
**Audience**: future agents / humans considering similar work; the project lead
**Companion**: `SESSION_2026-04-25_FINAL_REPORT.md`, `PHASE_TIMELINE.md`, `COWORK_FINDINGS.md`

---

## 0. Why this document exists

The session produced an unusual amount of output: 407 phases, 38 Lean blocks, 18 PR-ready files, 17 surface docs, 23 Findings. Distilling **what worked** and **what didn't** is independently valuable — both for the project lead's decisions and for future sessions following similar patterns.

This document is not a session summary (see `SESSION_2026-04-25_FINAL_REPORT.md`) nor a chronology (see `PHASE_TIMELINE.md`). It is a **forward-facing reflection**: meta-observations about the *process*, not the *output*.

---

## 1. Patterns that worked

### 1.1 Hypothesis-conditioning as a governance pattern

**Observation**: twice during the session, a Lean theorem's first version reached for an unproved fact and admitted a `sorry`:

- **Phase 437**: `polyakov_invariant_iff_zero` reached for `centerElement N 1 ≠ 1` from `N ≥ 2` (a `Complex.exp` periodicity calculation).
- **Phase 444**: `genusSuppression_asymptotic_zero` reached for `1/N²ᵍ → 0` as `N_c → ∞` (a `Filter.Tendsto` machinery argument).

In **both cases**, the resolution was the same: **rewrite the theorem to take the unproved fact as an explicit hypothesis-conditioned input** rather than admit it inline.

- Phase 437 → `polyakov_invariant_implies_zero` with `ω ≠ 1` as input.
- Phase 444 → `genusSuppression_le_quarter` with the uniform bound (sharp at `N_c = 2, g = 1`) replacing the asymptotic.

**Lesson**: when a Lean proof reaches for an unproved fact, **hypothesis-condition rather than admit**. The unproved fact gets named, surfaced, and becomes a future agent's tractable subgoal. The 0-sorry discipline catches this kind of over-reach immediately, and hypothesis-conditioning preserves the physical content without fake completion.

This is the project's **signature governance pattern** and it observed working twice in this session.

### 1.2 Long-cycle Lean blocks scaled well

**Observation**: 35 Bloque-4 blocks (L7-L41) followed a consistent `MasterCapstone.lean`-style closure pattern. The 3 physics-anchoring blocks (L42, L43, L44) followed the same template.

The template:
- 3-10 atomic-content files per block.
- Each file has a clear scope (one concept, one bound, one structure).
- Each block ends with a `MasterCapstone.lean` that combines the prior files into one packaged theorem.
- Blocks reference prior blocks via clean import statements.

**Lesson**: this template scales to ~40 blocks comfortably and produces output that's individually navigable. Future agents adopting it should keep the per-block scope modest (3-10 files) and produce a master capstone for each.

### 1.3 Bidirectional Mathlib relationship

**Observation**: the project documented Mathlib gaps (`MATHLIB_GAPS.md`) inward and Mathlib contributions (`MATHLIB_PRS_OVERVIEW.md`) outward. Phase 422 added an explicit cross-reference between them.

**Lesson**: a project that consumes from and contributes to Mathlib should document **both directions explicitly**. A single combined document would mix the two flows; separating them makes the asymmetry visible (we're net contributors here, with 18 outward vs 5 inward).

### 1.4 Surface-doc propagation pattern

**Observation**: every major arc (Mathlib upstream, L42, L43, L44) was followed by a propagation phase that pushed its content into:
- `BLOQUE4_LEAN_REALIZATION.md` (master narrative)
- `FINAL_HANDOFF.md` (TL;DR)
- `STATE_OF_THE_PROJECT.md` (snapshot)
- `COWORK_FINDINGS.md` (findings log)
- `NEXT_SESSION.md` (orientation)
- `SESSION_2026-04-25_FINAL_REPORT.md` (synthesis)
- README.md §11 (discoverability)

**Lesson**: an arc's value is only realised if the surface docs reflect it. **Budget ~1 phase per arc for propagation**. Without this, the work is invisible to anyone landing on the project.

The session executed this consistently. As a result, every doc is internally consistent at session-end (every major doc reflects 38 blocks, 18 PR-ready files, 23 Findings).

### 1.5 Triple-view confinement emerged naturally

**Observation**: the physics-anchoring blocks were not pre-planned as a triple. L42 came first (continuous view), L43 followed naturally (discrete view), L44 closed the triple (asymptotic view). The synthesis doc `TRIPLE_VIEW_CONFINEMENT.md` was written only after L44 was complete.

**Lesson**: when scaffolding around a single physics phenomenon (here, confinement), it pays off to formalise **multiple complementary views**. Each view illuminates a different mathematical structure and uncovers different open problems.

---

## 2. Patterns that didn't work / limitations observed

### 2.1 No `lake build` verification

**Observation**: the session produced ~321 Lean files and 18 PR-ready files **without running `lake build`** at any point. The workspace lacks `lake`.

**Limitation**: every Lean file produced is **structurally drafted**, not verified. Tactic-name drift, signature changes, and import drift are real and unmeasured. The project relies on Codex daemon's parallel verification, but no end-to-end Cowork-side verification exists.

**Lesson**: a session of this scale should ideally have **build-environment access at least intermittently**. Even one `lake build` per arc would have caught issues earlier. Future sessions should budget for this if possible. (Phase 451 produced `BUILD_VERIFICATION_PROTOCOL.md` to address this for future agents with build access.)

### 2.2 Diminishing returns on additional PR-ready files

**Observation**: PR-ready files 1-15 were each meaningfully different (covering different `Real.exp` / `Real.log` / hyperbolic / matrix lemmas). Files 16-18 were rearrangements of existing bounds (e.g., Phase 453's `exp(x) - 1 ≤ x/(1-x)` is a corollary of Phase 414's `exp(x) ≤ 1/(1-x)`).

**Limitation**: the PR-ready collection saturated around 15-17 files. Adding more produces increasingly derivative content.

**Lesson**: when an arc reaches saturation, **switch direction rather than continue**. The session did this (transitioned to L42 anchor block at Phase 427) but only after the user prompted continued output. Future sessions should self-trigger direction changes more proactively.

### 2.3 Surface-doc count grew unbounded

**Observation**: the session produced 17 surface docs in `mathlib_pr_drafts/INDEX.md` + root-level docs. Each doc has its own scope and audience, but together they require ~30 minutes for a new agent to navigate.

**Limitation**: the discoverability stack is well-organised but **dense**. A new agent might miss key information without explicit guidance.

**Lesson**: budget for a **`DOC_INDEX.md` consolidation phase** at session-end that lists all docs with their scope and audience. The session did partial work here (e.g., `mathlib_pr_drafts/INDEX.md` covers the PR drafts; `NEXT_SESSION.md` covers orientation) but a full top-level doc index would help.

### 2.4 The triple-view characterisation is structurally complete but substantively empty

**Observation**: L42 + L43 + L44 each input dimensionless constants (`c_Y`, `c_σ`, `ω ≠ 1`, etc.) as anchor structures, **NOT derived from first principles**. Each block's master theorem is `True`-shaped at the conceptual signpost level.

**Limitation**: the triple-view formalises three views that are all hypothesis-conditioned. Substantively connecting them — proving they describe the same physical phenomenon — requires the actual SU(N) Yang-Mills measure, which the project does not yet provide.

**Lesson**: structural Lean scaffolding has **value only when followed by substantive content**. Future sessions should resist the temptation to produce more structural scaffolding when the substantive prerequisites are open. (Phase 452's `OPEN_QUESTIONS.md` documents the substantive prerequisites.)

### 2.5 The % Clay incondicional metric did not advance

**Observation**: the metric advanced from ~12% → ~32% in the L30-L41 attack programme arc (Phases 283-402). Phases 403-454 (~52 phases of subsequent work) **did not advance the metric** — they produced PR-ready drafts, structural physics anchoring, and synthesis docs, all valuable but not retiring named frontier entries.

**Limitation**: the project's metric of progress is "named-frontier retirement". Structural / supporting / contextual work doesn't move it. Continuous "continúa!" prompting can produce arbitrary amounts of valuable structural work without metric-advancing content.

**Lesson**: the metric is a useful guardrail. Future sessions should **explicitly set goals against the metric** when continuing high-output cycles, to ensure the work direction is metric-tracked rather than structurally drifting.

---

## 3. Process observations

### 3.1 Phase volume per arc

| Arc | Phases | Output |
|---|---|---|
| Foundational Lean (L7-L13) | 79 phases | 7 blocks |
| Substantive deep-dives (L14-L29) | 155 phases | 16 blocks |
| Attack programme (L30-L41) | 120 phases | 12 blocks |
| Mathlib upstream | 24 phases | 11 PR files + infrastructure |
| L42 lattice QCD | 10 phases | 5 files + propagation |
| L43 + L44 physics-anchoring | 11 phases | 6 files + propagation |
| Final synthesis | 7 phases | 4 docs (TRIPLE_VIEW, README §11, TIMELINE, OPEN_QUESTIONS, etc.) |

**Observation**: throughput dropped from ~1 block per 5-10 phases (Lean) to ~1 file per 1-2 phases (PR-ready) to ~1 doc per phase (synthesis). This is **inverse to substance**: the more synthetic the work, the more it costs in phases.

**Lesson**: future sessions can use this calibration. Budget more phases when starting a new substantive Lean direction; budget fewer when in synthesis mode.

### 3.2 Sorry-catch frequency

2 sorry-catches in 407 phases ≈ **1 every 200 phases**. Both occurred in the physics-anchoring arc (L43, L44) where complex `Complex.exp` and `Filter.Tendsto` machinery was reached for. None occurred in the L7-L41 attack programme arc, suggesting that arc was within the project's safe complexity.

**Observation**: complexity can be predicted by the kind of mathematical machinery a theorem reaches for. `Complex.exp` periodicity, `Filter.Tendsto` asymptotic, and similar high-level tactics are sorry-catch hotspots.

**Lesson**: when reaching for high-level Mathlib machinery, **expect** to hypothesis-condition rather than admit. Plan for it.

### 3.3 Cowork ↔ Codex daemon parallelism

**Observation**: throughout the session, the Codex daemon ran in parallel (~150 commits/day). The Cowork session focused on **structural / synthetic work** that complements Codex's substantive Lean infrastructure.

**Limitation**: no Cowork phase verified Codex's parallel work. The Codex `BalabanRG/` 222-file infrastructure was wired into Cowork's master narrative (L13_CodexBridge) but not built locally.

**Lesson**: an explicit **cross-verification phase** between Cowork and Codex outputs (e.g., monthly) would catch infrastructure misalignments early. Currently this is informal.

---

## 4. What this session does NOT teach

- **Whether the project's overall strategy is correct**. The session formalises and consolidates an existing strategy (Eriksson's Bloque-4 paper); it does not validate or invalidate the strategy itself.
- **Whether the 18 PR-ready files will land upstream**. None has been built; the upstream contribution arc is queued, not executed.
- **Whether the 38 Lean blocks actually `lake build`**. No build was run.
- **Whether the literal Clay incondicional metric will continue advancing**. The session paused at ~32%; future advances depend on substantive physics work outside the session's scope.

---

## 5. Recommended actions for future sessions

Based on the patterns observed:

1. **Budget time for `lake build` access**. If possible, even intermittently. Catches drift early.
2. **Explicitly set goals against the metric**. Avoid open-ended "continúa!" without metric tracking.
3. **Switch directions when an arc saturates**. Don't continue in the same arc past diminishing returns.
4. **Hypothesis-condition early, not later**. When reaching for unproved facts, surface them as hypotheses immediately rather than wait for sorry-catch.
5. **Propagate after every major arc**. Surface-doc consistency is essential.
6. **Document open questions explicitly** (`OPEN_QUESTIONS.md` pattern). Future agents need this.
7. **Consider whether structural scaffolding is the right move**. If substantive prerequisites are missing, structural work risks being a sandbox.

---

## 6. Honest closing observation

The session produced **a lot of polished structural / synthetic output**. None of it advances the literal Clay statement directly. The value lies in:

- **For the project**: 38 well-organised Lean blocks + 18 PR-ready files + 17 navigable surface docs.
- **For the formalised math community**: 18 Mathlib upstream contribution drafts (pending build verification).
- **For future agents**: complete discoverability stack + `OPEN_QUESTIONS.md` + `BUILD_VERIFICATION_PROTOCOL.md` + `MATHLIB_SUBMISSION_PLAYBOOK.md`.

Whether this is "enough" is the project lead's call. The session demonstrates that an LLM-assisted Cowork session can sustain ~400 phases of consistent structural quality, with **two sorry-catches** caught and remediated, **no axioms** introduced outside `Experimental/`, and **bidirectional discoverability** documented end-to-end.

It does NOT demonstrate the substantive math content has been advanced. That remains future work.

---

*Cross-references*: `SESSION_2026-04-25_FINAL_REPORT.md`, `PHASE_TIMELINE.md`, `OPEN_QUESTIONS.md`, `BUILD_VERIFICATION_PROTOCOL.md`, `COWORK_FINDINGS.md` Findings 020-023.
