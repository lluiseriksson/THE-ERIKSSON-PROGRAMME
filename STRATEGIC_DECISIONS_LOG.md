# STRATEGIC_DECISIONS_LOG.md

**Purpose**: append-only log of major strategic decisions made by
Lluis (or by agreement between Lluis and the Cowork agent) about
the project's direction. Each entry documents the date, the
options considered, the choice made, and the rationale.

**How this differs from related docs**:
- `COWORK_FINDINGS.md` records **discoveries** (something is
  wrong / needs attention).
- `STRATEGIC_DECISIONS_LOG.md` records **resolutions** (we choose
  to do X about it).
- `AXIOM_FRONTIER.md` records **executions** (X was implemented as
  v1.Y.Z).

**Audience**: Lluis (own record), Cowork agent (continuity), future
auditors / reviewers reconstructing why the project is shaped the
way it is.

**Format**: most recent at top.

---

## Decision 010 — Honest metric tracking (structural ≠ substantive)
**Date**: 2026-04-25 (validated by Phases 403-465)
**Options considered**:
- A. Treat all output (structural + substantive) as advancing the project equally.
- B. Distinguish structural from substantive; only retire of named frontier entries advances strict-Clay incondicional %.
**Choice**: B.
**Rationale**: structural work (PR-ready, anchor blocks, surface docs, findings) is valuable but does not retire frontier entries. Conflating with substantive work would create misleading progress signals. Validated empirically: Phases 403-465 produced extensive structural output with **0% strict-Clay metric advance** (~32% throughout).
**Cross-references**: `DECISIONS.md` ADR-011, `LESSONS_LEARNED.md` §2.5, `MID_TERM_STATUS_REPORT.md` §9.4.

---

## Decision 009 — Surface-doc propagation per arc (structural integrity)
**Date**: 2026-04-25 (Phases 411, 432-435, 440-447, 462)
**Options considered**:
- A. Produce arc output; let surface docs go stale.
- B. Budget 1-2 propagation phases per arc to push content into 7 canonical surface docs.
**Choice**: B.
**Rationale**: arc value is realised only when surface docs reflect it. Without propagation, content is invisible to anyone landing on the project. Cost: 1-2 phases per arc; benefit: end-of-session consistency across all surface docs.
**Cross-references**: `DECISIONS.md` ADR-010, `CONTRIBUTING_FOR_AGENTS.md` §11.4, `LESSONS_LEARNED.md` §1.4.

---

## Decision 008 — Bidirectional Mathlib documentation (downstream + upstream)
**Date**: 2026-04-25 (Phase 415 + Phase 422 audit)
**Options considered**:
- A. Single combined doc covering Mathlib relationship.
- B. Separate `MATHLIB_GAPS.md` (downstream) + `MATHLIB_PRS_OVERVIEW.md` (upstream) with explicit cross-reference.
**Choice**: B.
**Rationale**: separating the two flows makes the asymmetry visible (project is net contributor: 18 outward vs 5 inward). Forces honest tracking of both consumption and contribution. Cross-reference audit (Phase 422) explicitly maps gaps to drafts.
**Cross-references**: `DECISIONS.md` ADR-009, `MATHLIB_GAPS.md`, `MATHLIB_PRS_OVERVIEW.md`.

---

## Decision 007 — Triple-view physics-anchoring (L42 + L43 + L44)
**Date**: 2026-04-25 (Phases 427-445)
**Options considered**:
- A. Single physics-anchoring block (e.g., area law only).
- B. Triple-view block (continuous + discrete + asymptotic) — 11 Lean files across 3 directories.
**Choice**: B.
**Rationale**: a single view emphasises one mathematical structure; three complementary views illuminate different mathematical structures and uncover different open problems (area law from first principles, non-zero `⟨P⟩` for deconfined phase, planar resummation in 4D). Each view independently formalisable.
**Trade-off**: 11 files instead of 5; partly redundant; each block's substantive content is hypothesis-conditioned.
**Cross-references**: `DECISIONS.md` ADR-008, `BLOQUE4_LEAN_REALIZATION.md` §"L42-L44 anchor blocks", `TRIPLE_VIEW_CONFINEMENT.md`.

---

## Decision 006 — Hypothesis-conditioning over sorry-admission
**Date**: 2026-04-25 (validated by Phases 437 + 444 sorry-catches)
**Options considered**:
- A. Admit `sorry` when proof reaches for unproved high-level machinery; address later.
- B. Rewrite theorem to take unproved fact as explicit hypothesis-conditioned input.
**Choice**: B.
**Rationale**: 0-sorry discipline is the project's signature pattern. Admitting sorries would erode it. Hypothesis-conditioning preserves physical content, names the gap, and makes it tractable for future agents. Validated twice in 2026-04-25 session (Phase 437 → Phase 458 closure example demonstrates the two-stage pattern).
**Cross-references**: `DECISIONS.md` ADR-007, `COWORK_FINDINGS.md` Findings 022 + 023 + 024, `LESSONS_LEARNED.md` §1.1.

---

## Decision 005 — Continuum-trick disclosure adopted (Option B)

- **Date**: 2026-04-25
- **Context**: `COWORK_FINDINGS.md` Finding 004 surfaced that
  `ClayYangMillsPhysicalStrong`'s `HasContinuumMassGap` field is
  satisfied via the coordinated scaling
  `latticeSpacing N = 1/(N+1) ↔ constantMassProfile m N = m/(N+1)`,
  not via genuine continuum analysis.
- **Options considered** (per `GENUINE_CONTINUUM_DESIGN.md` §5):
  - **Option A**: implement `ClayYangMillsPhysicalStrong_Genuine`
    as a Lean predicate now, mark the no-witness case as an axiom
    for documentation.
  - **Option B**: document the caveat in strategic narrative only;
    no Lean changes; preserve 0-axiom invariant.
  - **Option C**: refactor `HasContinuumMassGap` to take a
    `LatticeSpacingScheme` parameter, making the distinction
    first-class in the type system.
- **Choice**: **Option B** for now, **Option C eventually before
  any external Clay announcement**.
- **Rationale**:
  - Option B preserves the 0-axiom invariant which is more valuable
    than the type-level distinction at this phase.
  - Option C is a ~400 LOC refactor that should land in the
    "honesty refactor" wave that ships alongside any external
    announcement.
  - Strategic docs (Finding 004 +
    `GENUINE_CONTINUUM_DESIGN.md` + the new caveats in
    `STATE_OF_THE_PROJECT.md`, `MATHEMATICAL_REVIEWERS_COMPANION.md`,
    `MID_TERM_STATUS_REPORT.md`) provide adequate disclosure for
    current-phase external readers.
- **Executed**:
  - Cowork agent added caveat paragraphs to STATE_OF_THE_PROJECT,
    MATHEMATICAL_REVIEWERS_COMPANION (§6.2), and
    MID_TERM_STATUS_REPORT (§4.2.1).
  - Finding 004 status updated to record actions 1+2 done; action 3
    addressed via design proposal.

---

## Decision 004 — PR drafts deferred to background, not blocking

- **Date**: 2026-04-25
- **Context**: `MATHLIB_GAPS.md` identified 5 Mathlib gaps relevant
  to the project. Three PR drafts have been written
  (`mathlib_pr_drafts/AnimalCount.lean`,
  `PiDisjointFactorisation.lean`, `PartitionLatticeMobius.lean`).
- **Options considered**:
  - Push all drafts upstream now via Lluis as primary author.
  - Have Codex push them as part of routine work.
  - Defer until after F3 closure; treat as background.
- **Choice**: **defer until after F3 closure**. PR drafts remain
  in `mathlib_pr_drafts/` as ready-to-go but not yet submitted.
- **Rationale**:
  - The drafts are not blocking the in-repo F3 work (the in-repo
    workarounds exist).
  - Mathlib PR review takes weeks; better to land them after the
    main project work is closer to completion so the PR
    descriptions can reference the published Lean repository.
  - Codex's bandwidth is best spent on F3 progress, not Mathlib
    PR shepherding.
- **Executed**: drafts remain in `mathlib_pr_drafts/`. No upstream
  action yet.

---

## Decision 003 — F3-Count Resolution C adopted (over A and B)

- **Date**: 2026-04-25 morning
- **Context**: `BLUEPRINT_F3Count.md` Finding 001 surfaced that the
  polynomial frontier `ShiftedConnectingClusterCountBound C_conn dim`
  was structurally infeasible. Three resolutions were proposed (§3 of
  the blueprint).
- **Options considered**:
  - **Resolution A**: keep polynomial form, restrict to `Dim 4`.
    (Ruled out: same infeasibility.)
  - **Resolution B**: rebrand the activity rate `r` to absorb the
    lattice exponential. (Workable but obscure.)
  - **Resolution C**: replace the polynomial frontier with an
    exponential one `count(n) ≤ C_conn · K^n`, paired with the
    smallness `K · r < 1`. (Standard KP form from the literature.)
- **Choice**: **Resolution C**.
- **Rationale**: matches the form actually proved in Brydges-Kennedy
  / Kotecký-Preiss / Friedli-Velenik; cleanest API; minimal
  workaround.
- **Executed**: Codex implemented Resolution C across v1.79.0 →
  v1.82.0 within ~3-4 hours. Validated in
  `CODEX_EXECUTION_AUDIT.md`. Blueprint §−1 update overlay added.

---

## Decision 002 — Peter–Weyl reclassified as aspirational / Mathlib-PR

- **Date**: 2026-04-22 evening
- **Context**: consumer-driven recon of
  `YangMills/ClayCore/CharacterExpansion.lean` and adjacent files
  found that `CharacterExpansionData.{Rep, character, coeff}` were
  vestigial metadata (filled with `PUnit / 0 / 0`). Only
  `h_correlator` flowed downstream to Clay.
- **Options considered**:
  - Continue the original 6-layer Peter-Weyl roadmap (~6,100-13,100
    LOC of formalisation).
  - Pivot to working in the scalar-trace subalgebra (already
    covered by L2.5 + L2.6 + sidecars 3a/3b/3c).
- **Choice**: **pivot**. Reclassify Peter-Weyl as aspirational /
  Mathlib-PR, not Clay-blocking.
- **Rationale**:
  - The downstream consumer (`ClusterCorrelatorBound`) only needs
    the scalar-trace data, which is already provable.
  - Avoids a ~6-12 month Mathlib-scale formalisation sub-project
    that is not on the critical path.
- **Executed**:
  - L2.6 closed at 100% via the sidecar route.
  - `PETER_WEYL_ROADMAP.md` annotated with the reclassification
    banner (still 574 lines until 2026-04-25 trim).
  - `PETER_WEYL_AUDIT.md` (Cowork agent) verified the
    reclassification holds as of 2026-04-25.

---

## Decision 001 — Strict 0-axiom invariant outside Experimental

- **Date**: ~2026-04-14 (v0.32.0 / v0.33.0 axiom-elimination
  campaign)
- **Context**: the project formerly had a monolithic axiom
  `yangMills_continuum_mass_gap` that effectively axiomatised the
  Clay statement. Plus `lsi_normalized_gibbs_from_haar` and various
  smaller axioms.
- **Options considered**:
  - Keep the axioms as honest documentation of remaining gaps.
  - Aggressively eliminate all axioms outside `Experimental/`.
- **Choice**: **strict 0-axiom invariant outside `Experimental/`**.
  Genuine open analytic gaps are surfaced as **theorem-side
  hypotheses** or as **named structures with no witness**, not as
  `axiom` declarations.
- **Rationale**:
  - Axioms can hide assumptions; theorem-side hypotheses are
    explicit at the use site.
  - Vacuous endpoints (`ClayYangMillsTheorem` etc.) audited as
    such, preventing accidental over-claiming.
  - The 0-axiom claim is a strong signal of formal honesty.
- **Executed**:
  - The monolithic axiom was deleted (v0.32.0).
  - `lsi_normalized_gibbs_from_haar` was eliminated (v0.34+
    cleanup, completed by v0.97).
  - The 14 axioms now in `Experimental/` are the project's honest
    remaining gaps. See `EXPERIMENTAL_AXIOMS_AUDIT.md` for the
    classification.
  - Discipline encoded in `CODEX_CONSTRAINT_CONTRACT.md` HR3.

---

## Decision 000 — Adopt blueprint → execution → audit governance

- **Date**: ~2026-04-25 morning (start of the Cowork ↔ Codex
  governance system)
- **Context**: Codex daemon was producing ~150 commits/day with
  variable patterns of substantive vs canary work. Lluis wanted
  a way to keep throughput high but ensure direction.
- **Options considered**:
  - Manual oversight only (Lluis reads the daily log).
  - Automated CI checks only (no human-readable strategy docs).
  - **Hybrid**: Cowork agent writes blueprints + audits + contract;
    Codex executes; daily auto-audit checks compliance; Lluis
    intervenes on flagged issues.
- **Choice**: **hybrid**.
- **Rationale**:
  - Cowork agent's strength is depth (blueprints, findings, audits).
  - Codex's strength is throughput (Lean coding, CI loops).
  - Together they form a complete loop with checks at each layer.
- **Executed**:
  - `CODEX_CONSTRAINT_CONTRACT.md` written with HR/SR rules and
    priority queue.
  - `eriksson-daily-audit` scheduled task running at 09:04 local.
  - `COWORK_FINDINGS.md` log structure for obstructions.
  - `CONTRIBUTING_FOR_AGENTS.md` operational guidelines.
  - `AGENT_HANDOFF.md` continuity document.
  - Empirical validation: F3-Count Resolution C cycle (Decision 003)
    completed in ~3-4 hours blueprint-to-execution.

---

## Format for new entries

```markdown
## Decision <N> — <one-line subject>

- **Date**: YYYY-MM-DD (or YYYY-MM-DD afternoon, etc.)
- **Context**: 1-2 sentences on what surfaced the question.
- **Options considered**:
  - Option A: brief description.
  - Option B: brief description.
  - Option C: brief description.
- **Choice**: which option.
- **Rationale**: 1-3 sentences on why.
- **Executed**: what concretely was done as a result.
```

Append above the format-block, below the most recent entry.

---

## Notes for future entries

- Decisions about **renames** (file names, structure names) belong
  here.
- Decisions about **scope changes** (add/remove a target) belong
  here.
- Decisions about **axiom retirement** belong here.
- Decisions about **architecture shifts** (e.g., Resolution C-style
  pivots) belong here.
- Decisions about **pure code edits** (refactor a single function)
  do **not** belong here — use git history.
- Decisions about **process changes** (e.g., the contract version
  bumped from v1 to v2) belong here.

---

*Maintained by Cowork agent and Lluis. Started 2026-04-25.*
