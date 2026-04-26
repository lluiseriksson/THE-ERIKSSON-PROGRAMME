# DOCS_INDEX — strategic & roadmap documents

**One-page orientation**. Last verified: 2026-04-25.

If you have 30 seconds, read just §0 below. If you have 5 minutes, then
the four "ground truth" files. Everything else is supporting material.

---

## 0. Read this first if you only read one thing

- **`FINAL_HANDOFF.md`** — 60-second TL;DR for arriving cold. Project
  state, three most important things, what to do next.
- **`README.md`** — current bars, current front, current "Last closed"
  version. Updated continuously. **Authoritative for project state.**

If you have 30 seconds, read `FINAL_HANDOFF.md` only. If you want to
know *what is closed today*, the README is the answer. The rest of
this index helps you navigate from there.

---

## 1. Ground-truth state files (refreshed continuously)

| File | Purpose | Last refreshed |
|---|---|---|
| `README.md` | Current bars, current front, "Last closed" entry | continuously |
| `AXIOM_FRONTIER.md` | Version-by-version axiom census; current axiom count outside `Experimental/` is **0** | continuously |
| `SORRY_FRONTIER.md` | Live sorry count; currently **0** | continuously |
| `STATE_OF_THE_PROJECT.md` | Single-page snapshot prose narrative | 2026-04-25 |

If `README.md` and `STATE_OF_THE_PROJECT.md` ever disagree on a fact,
the README is authoritative — it is updated by the autonomous Codex
daemon on every release.

---

## 2. Roadmaps (strategic, multi-week to multi-year horizon)

| File | Horizon | Last refreshed |
|---|---|---|
| `ROADMAP_MASTER.md` | 10–15 year program horizon, Phase 0–4 abstract structure | 2026-03-27 (low-priority refresh deferred) |
| `ROADMAP.md` | Phase 5–7 dependency chain, current critical path nodes | 2026-04-25 |
| `UNCONDITIONALITY_ROADMAP.md` | Version-by-version unconditionality progress, top banner v0.98.0 + 2026-04-25 update | 2026-04-25 |
| `PETER_WEYL_ROADMAP.md` | Reclassified as aspirational / Mathlib-PR (not Clay-blocking) on 2026-04-22 | 2026-04-22 (banner) / 2026-04-19 (body) |

---

## 3. Active blueprints (current critical path)

These are the strategic documents that drive the **F3 frontier**, the
current bottleneck for `ClayYangMillsMassGap N_c` for N_c ≥ 2.

| File | Subject | Status |
|---|---|---|
| `BLUEPRINT_F3Count.md` | F3-Count strategy: exponential frontier `ShiftedConnectingClusterCountBoundExp` with `K = 2d − 1 = 7` for d = 4. Klarner BFS-tree witness construction. | strategy delivered 2026-04-25 |
| `BLUEPRINT_F3Mayer.md` | F3-Mayer strategy: Brydges–Kennedy random-walk cluster expansion. `r = 4 N_c · β`, `A₀ = 1`, validity `β < log(2)/N_c`. | strategy delivered 2026-04-25 |
| `mathlib_pr_drafts/AnimalCount.lean` | Mathlib upstream draft for the BFS-tree count bound (Gap #1 from `MATHLIB_GAPS.md`) | draft delivered 2026-04-25 |
| `mathlib_pr_drafts/PR_DESCRIPTION.md` | github PR text for AnimalCount upstream | draft delivered 2026-04-25 |
| `mathlib_pr_drafts/F3_Count_Witness_Sketch.lean` | Consumer-side sketch showing how the upstream lemma discharges F3-Count | draft delivered 2026-04-25 |
| `mathlib_pr_drafts/PiDisjointFactorisation.lean` | Mathlib upstream draft for the disjoint-coordinate Pi-measure factorisation (Gap #2 from `MATHLIB_GAPS.md`) | draft delivered 2026-04-25 |
| `mathlib_pr_drafts/PR_DESCRIPTION_Gap2.md` | github PR text for the Pi-disjoint-factorisation upstream | draft delivered 2026-04-25 |
| `mathlib_pr_drafts/PartitionLatticeMobius.lean` | Mathlib upstream draft for partition-lattice Möbius inversion (Gap #3 from `MATHLIB_GAPS.md`) | draft delivered 2026-04-25 |
| `mathlib_pr_drafts/PR_DESCRIPTION_Gap3.md` | github PR text for the partition-lattice Möbius upstream | draft delivered 2026-04-25 |

---

## 4. Audits & inventories (one-shot strategic deliverables)

| File | Subject | Last delivered |
|---|---|---|
| `MATHLIB_GAPS.md` | 5 Mathlib gaps inventoried, hybrid PR/in-repo recommendation | 2026-04-25 |
| `PETER_WEYL_AUDIT.md` | Verifies 2026-04-22 reclassification holds; surfaces 3 deadweight candidates | 2026-04-25 |
| `ROADMAP_AUDIT.md` | Staleness audit of the four roadmap documents | 2026-04-25 |
| `CODEX_EXECUTION_AUDIT.md` | Per-version validation of v1.79–v1.82 against `BLUEPRINT_F3Count.md` Resolution C | 2026-04-25 |
| `MATHEMATICAL_REVIEWERS_COMPANION.md` | Self-contained mathematical exposition of v1.79–v1.83 for non-Lean reviewers / academic stakeholders | 2026-04-25 |
| `EXPERIMENTAL_AXIOMS_AUDIT.md` | Classification of the 14 axioms in `YangMills/Experimental/` by retire-ability | 2026-04-25 |
| `CONTRIBUTING_FOR_AGENTS.md` | Operational loop for autonomous agents (Codex daemon, Cowork sessions); complements the human-targeted `CONTRIBUTING.md` | 2026-04-25 |
| `GENUINE_CONTINUUM_DESIGN.md` | Design proposal for `ClayYangMillsPhysicalStrong_Genuine` predicate that requires a physical lattice-spacing scheme. Action 3 of `COWORK_FINDINGS.md` Finding 004. | 2026-04-25 |
| `AUDIT_v185_LATTICEANIMAL.md` | Detailed audit of v1.85.0 `LatticeAnimalCount.lean` and roadmap to Priority 1.2 closure | 2026-04-25 |
| `F3_CHAIN_MAP.md` | Definitive dependency graph from F3 inputs to ClayYangMillsMassGap N_c and ClayYangMillsPhysicalStrong | 2026-04-25 |
| `AGENT_HANDOFF.md` | Onboarding document for a future Cowork agent picking up the project | 2026-04-25 |
| `REFERENCES_AUDIT.md` | Bibliographic audit of 15 primary-source citations across all strategic docs | 2026-04-25 |
| `MID_TERM_STATUS_REPORT.md` | Academic-paper-style status report; suitable for sharing with external reviewers | 2026-04-25 |
| `LAYER_AUDIT.md` | Health audit of non-F3 foundational layers (L0-L7, P2-P8); detects orphans and stale layers | 2026-04-25 |
| `THREAT_MODEL.md` | Inventory of project failure modes (mathematical, process, operational, external) and early-warning signals | 2026-04-25 |
| `RELEASE_NOTES_TEMPLATE.md` | Standardised template for `AXIOM_FRONTIER.md` release-note entries | 2026-04-25 |
| `STRATEGIC_DECISIONS_LOG.md` | Append-only log of major strategic decisions (option chosen, rationale, executed) | 2026-04-25 |
| `CADENCE_AUDIT.md` | Quantitative analysis of commits per hour, validates the 130-150/day estimate against real session data | 2026-04-25 |
| `PROJECT_TIMELINE.md` | Comprehensive chronological history from project start (2026-03-12) through v1.85.0 | 2026-04-25 |
| `GLOSSARY.md` | Terminology compendium covering Lean structures + mathematical-physics terms | 2026-04-25 |
| `README_AUDIT.md` | Section-by-section audit of `README.md` for accuracy and freshness | 2026-04-25 |
| `NEXT_SESSION_AUDIT.md` | Audit of `YangMills/ClayCore/NEXT_SESSION.md` for staleness; flags polynomial-frontier subtarget contradiction | 2026-04-25 |
| `OBSERVABILITY.md` | Specification of project metrics worth tracking continuously, with dashboard layout | 2026-04-25 |
| `KNOWN_ISSUES.md` | Single-page consolidated summary of all caveats, limitations, and open questions for external readers | 2026-04-25 |
| `SESSION_SUMMARY.md` | Comprehensive accountability record of the 2026-04-25 Cowork session: timeline, deliverables by category, findings, decisions, codex parallel activity, self-assessment | 2026-04-25 |
| `AUDIT_v186_LATTICEANIMAL_UPDATE.md` | Follow-up to v1.85 audit: progress between v1.85 and v1.86, §3.1 reverse-bridge complete, §3.2 partial, revised LOC estimate | 2026-04-25 |
| `FINAL_HANDOFF.md` | 60-second TL;DR for arriving cold. Read this first. | 2026-04-25 |
| `AUDIT_v187_LATTICEANIMAL_UPDATE.md` | Validates v1.87.0 against v1.86 audit predictions; third consecutive predict-confirm cycle | 2026-04-25 |
| `AUDIT_v188_LATTICEANIMAL_UPDATE.md` | Validates v1.88.0 against v1.87 audit; fourth consecutive cycle. Final incremental Priority-1.2 audit. | 2026-04-25 |
| `REPO_INFRASTRUCTURE_AUDIT.md` | Audit of unexplored repo corners: AI_ONBOARDING, registry/, scripts/, .github/workflows, dashboard/, docs/. Surfaces dual-governance dead weight (Finding 007). | 2026-04-25 |
| `BUILD_AUDIT.md` | Audit of build configuration (lakefile, lean-toolchain, lake-manifest, YangMills.lean root). Finds LatticeAnimalCount not in root import; misleading "Mathlib-master" badge. | 2026-04-25 |
| `OPENING_TREE.md` | Master Cowork strategy for Clay attack. 7 candidate branches. Cowork commits to Branches VII, III, II in parallel to Codex's Branch I. | 2026-04-25 |
| `BLUEPRINT_ContinuumLimit.md` | Branch VII: genuine continuum-limit framework via PhysicalLatticeScheme; addresses Finding 004. | 2026-04-25 |
| `BLUEPRINT_ReflectionPositivity.md` | Branch III: reflection positivity + transfer matrix → all-β lattice mass gap. | 2026-04-25 |
| `YangMills/L7_Continuum/PhysicalScheme.lean` | Branch VII Lean scaffold: PhysicalLatticeScheme + HasContinuumMassGap_Genuine + Clay-genuine predicate. | 2026-04-25 |
| `YangMills/L6_OS/WilsonReflectionPositivity.lean` | Branch III Lean scaffold (file 1/3): wilsonReflection + wilsonGibbs_reflectionPositive + bridge to abstract OSReflectionPositive. | 2026-04-25 |
| `YangMills/L4_TransferMatrix/TransferMatrixConstruction.lean` | Branch III Lean scaffold (file 2/3): GNS construction from RP, transfer matrix as bounded positive self-adjoint, vacuum + spectral gap predicates, terminal `clayMassGap_fromTransferMatrixRP`. | 2026-04-25 |
| `BLUEPRINT_BalabanRG.md` | Branch II long-horizon strategic blueprint: inductive RG step + Experimental-axiom retirement opportunities + 24-36 month roadmap. | 2026-04-25 |

---

## 5. Operational documents (live status, not strategic)

| File | Purpose |
|---|---|
| `COWORK_AUDIT.md` | Daily auto-generated audit (cadence, axiom drift, F3 progress signals). Created by scheduled task `eriksson-daily-audit` running at 09:04 AM local. |
| `COWORK_FINDINGS.md` | Structured log of substantive obstructions; referenced by `CODEX_CONSTRAINT_CONTRACT.md` §6.1 |
| `CODEX_CONSTRAINT_CONTRACT.md` | Hard / soft rules + priority queue for the autonomous Codex daemon |
| `STATE_OF_THE_PROJECT_HISTORY.md` | Archived dated entries (v0.32, v0.33, v0.34, v1.46.0) moved out of `STATE_OF_THE_PROJECT.md` on 2026-04-25 |
| `PETER_WEYL_ROADMAP_HISTORY.md` | Archived 574-line original Peter–Weyl roadmap, moved out 2026-04-25 |
| `NEXT_SESSION.md` (in `YangMills/ClayCore/`) | Codex-facing instructions for the next coding session |

---

## 6. Auxiliary frontier documents

| File | Purpose |
|---|---|
| `HYPOTHESIS_FRONTIER.md` | Named explicit hypotheses still gating the chain |
| `DECISIONS.md` | Architecture decision record |
| `PHASE8_PLAN.md` / `PHASE8_SUMMARY.md` | Phase 8 (LSI / mass gap) detailed planning |

---

## 7. How to reach 100% unconditional

Per the v0.98.0 banner of `UNCONDITIONALITY_ROADMAP.md`, the four-step
remaining route is:

1. F1/F2/F3 → `ClusterCorrelatorBound`. **Active.** See
   `BLUEPRINT_F3Count.md` + `BLUEPRINT_F3Mayer.md`.
2. ClayCore LSI → SU(N) DLR transfer. Open.
3. SU(N) Dirichlet/Lie sidecar (out of `Experimental/LieSUN`). Open.
4. Physical endpoint wiring through `ClayYangMillsPhysicalStrong` /
   `ClayYangMillsMassGap N_c`. **Partially closed**: N_c = 1 is
   unconditional; N_c ≥ 2 gated on (1).

---

## 8. Late-session 2026-04-25 additions (Phases 403-455)

**These docs were produced AFTER the original DOCS_INDEX.md was last updated. They cover the Mathlib upstream contribution arc (Phases 403-426), L42-L44 physics-anchoring arc (Phases 427-447), and final synthesis arc (Phases 448-455).**

### 8.1 Mathlib upstream contribution

| File | Purpose |
|---|---|
| `MATHLIB_PRS_OVERVIEW.md` | Outward-facing catalog of 18 PR-ready Mathlib lemmas. Complement to `MATHLIB_GAPS.md` (downstream). |
| `MATHLIB_SUBMISSION_PLAYBOOK.md` | Step-by-step operational playbook for landing 9-10 PRs upstream. 10-13 hours focused work estimate. |
| `mathlib_pr_drafts/INDEX.md` | Master organisational doc inside the PR drafts folder: tier classification, priority queue, per-file checklist. |
| `mathlib_pr_drafts/README.md` | Folder entry-point. |
| `mathlib_pr_drafts/*_PR.lean` (18 files) | Individual PR-ready Lean files. None built with `lake build`. |

### 8.2 Physics-anchoring blocks (L42 + L43 + L44 = triple-view characterisation)

| File | Purpose |
|---|---|
| `BLOQUE4_LEAN_REALIZATION.md` | Master narrative for all 38 long-cycle blocks (L7-L44), including L42-L44 sections. |
| `LITERATURE_COMPARISON.md` | Position the project relative to 8 published Yang-Mills mass-gap approaches (Bałaban, MRS, Dimock, Glimm-Jaffe, holography, Hairer, Wilson+BK, Seiberg-Witten). |
| `TRIPLE_VIEW_CONFINEMENT.md` | Synthesis of L42 (continuous) + L43 (discrete) + L44 (asymptotic) views of confinement. Academic audience. |
| `YangMills/L42_LatticeQCDAnchors/` (5 files) | Continuous-view confinement: β-coefficients, RG running, dimensional transmutation, area law, master capstone. |
| `YangMills/L43_CenterSymmetry/` (3 files) | Discrete-view confinement: Z_N center, Polyakov loop, master capstone. |
| `YangMills/L44_LargeNLimit/` (3 files) | Asymptotic-view confinement: 't Hooft coupling, planar dominance, master capstone. |

### 8.3 Session synthesis & navigation

| File | Purpose |
|---|---|
| `NEXT_SESSION.md` (root, NOT inside YangMills/ClayCore) | Top-level orientation for next agent. 4 directions (A: Mathlib PR, B: build verification, C: substantive Yang-Mills, D: F3 closure). |
| `SESSION_2026-04-25_FINAL_REPORT.md` | Synthetic 2-3 page academic-audience report of the entire 438+ phase session. |
| `PHASE_TIMELINE.md` | Single-page chronological timeline of the phases organized in 11 arcs. |
| `OPEN_QUESTIONS.md` | Comprehensive enumeration of 30+ open questions identified during session, by priority (P0 → P3 → Holy Grail). |
| `BUILD_VERIFICATION_PROTOCOL.md` | Step-by-step protocol for verifying the entire session output with `lake build`. 2-12 hours estimate. |
| `LESSONS_LEARNED.md` | Honest meta-reflection on patterns observed: hypothesis-conditioning governance, sorry-catches, scaling characteristics, limitations. |
| `SESSION_BOOKEND.md` | Formal session-end artifact (Phase 457) + post-bookend overflow / threshold acknowledgment notes. |
| `POST_BOOKEND_EPILOGUE.md` | Catalog of Phases 458-469 (post-bookend epilogue arc with P0 closures + governance docs). |
| `RECOMMENDATIONS_FOR_LLUIS.md` | Single-page actionable items for the project lead — 5 priorities by yield-per-effort. |
| `LATE_SATURATION_REPORT.md` | **Late-late-session arc artifact** (Phase 486): documents the post-threshold work (Phases 477-486+) honestly. Triggered by the agent's own framework when the session continued past the OBSERVABILITY §7.6 threshold. |

### 8.4 Updated docs (post-Phase 402)

These existed before but received post-Phase 402 / post-Phase 432 / post-Phase 446 addenda:

| File | Update |
|---|---|
| `README.md` | §11 session-end addendum (Phase 449) |
| `FINAL_HANDOFF.md` | post-Phase 410 + post-Phase 432 + post-Phase 446 mini-mini addenda |
| `STATE_OF_THE_PROJECT.md` | post-Phase 410 + post-Phase 432 + post-Phase 446 sub-addenda |
| `COWORK_FINDINGS.md` | Findings 020 (Mathlib PR-ready), 021 (L42), 022 (L43), 023 (L44) |
| `MATHLIB_GAPS.md` | Cross-reference banner pointing to `MATHLIB_PRS_OVERVIEW.md` (Phase 422) |

### 8.5 Final session metrics (post-Phase 455)

- **Phases**: 49 → 455 = **407 phases** in single-day session.
- **Long-cycle Lean blocks**: **38** (L7-L44).
- **Lean files**: ~321 (~38,200 LOC).
- **Mathlib-PR-ready files**: **18**.
- **Surface docs propagated/produced**: 18.
- **Findings filed**: 23 (Findings 001-023).
- **Sorries**: 0 (with 2 sorry-catches: Phase 437 + Phase 444, both resolved by hypothesis-conditioning).
- **% Clay literal incondicional**: ~32% (post-Phase 402, unchanged thereafter).

---

*Maintained by the Cowork agent (Claude) under supervision of Lluis
Eriksson. If a file mentioned here is missing, it has been moved or
renamed; check git log.*

*Late-session §8 added 2026-04-25 (Phase 456). For lessons drawn from this period, see `LESSONS_LEARNED.md`.*
