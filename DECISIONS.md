# DECISIONS

This file records architecture-level decisions.
Each decision should be append-only and referenced by ID.

---

## ADR-001 — Separate target track from infrastructure track
Status: accepted
Date: 2026-03-12

Decision:
The project is split conceptually into:
- a Yang–Mills target track,
- a reusable constructive QFT infrastructure track.

Reason:
This prevents confusion between general infrastructure progress and actual closure of the Yang–Mills critical path.

Consequences:
- every node must have `kind: target` or `kind: infrastructure`
- dashboards must report both tracks separately

---

## ADR-002 — Registry is the source of truth
Status: ~~accepted~~ **SUPERSEDED 2026-04-25** by Decision 000 of
`STRATEGIC_DECISIONS_LOG.md` (Adopt blueprint→execution→audit
governance). The `registry/` is no longer maintained; current
sources of truth are `STATE_OF_THE_PROJECT.md`,
`AXIOM_FRONTIER.md`, `COWORK_FINDINGS.md`, and the Lean code's
per-commit `#print axioms` traces. See `COWORK_FINDINGS.md`
Finding 008 for the supersession discussion.
Date: 2026-03-12 (original); 2026-04-25 (supersession noted).

Decision (original):
The machine-readable registry under `registry/` is the canonical project state.

Reason (original):
Human summaries drift. AI sessions lose context. The registry must dominate.

Consequences (original):
- summaries must be generated from or checked against registry data
- contradictions must fail CI where possible

Why superseded:
The registry pattern was abandoned in practice as the project
scaled (~275 ClayCore files vs ~30 registered nodes; registry
maintenance fell behind the pace of file creation). The
blueprint→audit pattern proved more workable. Per Finding 007 +
008, the registry is dead-weight pending Lluis decision on
archival vs refresh.

---

## ADR-003 — No undocumented axioms on main
Status: accepted
Date: 2026-03-12

Decision:
No `axiom` may appear in the main branch unless it is explicitly registered and justified.

Reason:
Undocumented axioms destroy epistemic integrity.

Consequences:
- CI must scan for axioms
- each registered imported theorem must have a corresponding node entry

---

## ADR-004 — Only kernel-certified theorems close critical nodes
Status: accepted
Date: 2026-03-12

Decision:
A critical node is closed only by `FORMALIZED_KERNEL`.

Reason:
External audits and tests are valuable but do not substitute for proof.

Consequences:
- `PROXY_TEST`, `AUDITED_EXTERNALLY`, `IMPORTED_AXIOM`, and `FORMALIZED_WEAK` cannot close a critical node

---

## ADR-005 — Anti-vacuity enforcement
Status: accepted
Date: 2026-03-12

Decision:
The project explicitly forbids vacuous closure on the critical path.

Reason:
This includes empty-domain arguments, trivial witnesses, packaging-only bridges, and parameter-passing disguised as proof.

Consequences:
- critical nodes must include anti-vacuity notes where relevant
- CI and review checklists must inspect for semantic trivialization

---

## ADR-006 — Build governance before Lean volume
Status: accepted
Date: 2026-03-12

Decision:
The project will build registry, dashboards, labels, and CI before adding significant Lean code.

Reason:
Without this, the repository risks repeating the failure mode of opaque research state.

Consequences:
- first milestone is architectural integrity, not theorem count

---

## ADR-007 — Hypothesis-conditioning over sorry-admission
Status: accepted
Date: 2026-04-25 (validated by Phases 437 + 444 sorry-catches)

Decision:
When a Lean proof reaches for unproved high-level machinery (e.g., `Complex.exp` periodicity, `Filter.Tendsto` asymptotic, deep matrix theory), the resolution is to **rewrite the theorem to take the unproved fact as an explicit hypothesis-conditioned input** rather than admit a `sorry`.

Reason:
The 0-sorry discipline is the project's signature governance pattern. Admitting sorries would erode it and create technical debt that's hard to surface. Hypothesis-conditioning preserves the physical content, names the gap, and makes it tractable for future agents.

Consequences:
- Theorems get longer signatures (more hypotheses) but no sorries.
- Hypothesis-conditioned subgoals are tracked in `OPEN_QUESTIONS.md` for later closure.
- Two-stage pattern emerges: hypothesis-condition first (immediate), close later (Phase 437 → Phase 458 example).
- Future agents have explicit, tractable subgoals rather than buried `sorry`s.

References: `COWORK_FINDINGS.md` Findings 022 + 023 + 024, `LESSONS_LEARNED.md` §1.1, `CONTRIBUTING_FOR_AGENTS.md` §11.1.

---

## ADR-008 — Triple-view physics-anchoring (L42 + L43 + L44)
Status: accepted
Date: 2026-04-25 (Phases 427-445)

Decision:
For pure Yang-Mills physics anchoring, formalise three structurally complementary views:
- **L42 (continuous)**: area law, dimensional transmutation, mass gap.
- **L43 (discrete)**: Z_N center symmetry, Polyakov loop.
- **L44 (asymptotic)**: 't Hooft 1/N expansion, planar dominance.

Reason:
A single view (e.g., area law alone) emphasises one mathematical structure. Three complementary views illuminate different mathematical structures and uncover different open problems. Each view's formalisation is independently valuable.

Consequences:
- 11 Lean files across 3 blocks (5 + 3 + 3) instead of a single block.
- Each block's master theorem is hypothesis-conditioned on dimensionless constants (`c_Y`, `c_σ`, `ω ≠ 1`, etc.).
- The `TRIPLE_VIEW_CONFINEMENT.md` synthesis document explains the conceptual bridge.
- Each view uncovers a distinct open problem (area law from first principles, non-zero `⟨P⟩` for deconfined phase, planar resummation in 4D).
- Substantive equivalence between views requires Wilson Gibbs measure analysis (P1 §2.6 + dependents).

References: `BLOQUE4_LEAN_REALIZATION.md` §"L42-L44 anchor blocks", `TRIPLE_VIEW_CONFINEMENT.md`, Findings 021 + 022 + 023.

---

## ADR-009 — Bidirectional Mathlib documentation
Status: accepted
Date: 2026-04-25 (Phase 415 produced `MATHLIB_PRS_OVERVIEW.md`; Phase 422 audited cross-reference)

Decision:
Document the project's relationship with Mathlib **explicitly in both directions**:
- **Downstream** (Mathlib → us): `MATHLIB_GAPS.md` lists what the project needs from Mathlib but Mathlib doesn't yet provide.
- **Upstream** (us → Mathlib): `MATHLIB_PRS_OVERVIEW.md` lists what the project contributes back to Mathlib.

Reason:
A single combined document would mix the two flows. Separating them makes the asymmetry visible (currently the project is a net contributor: 18 outward PR-ready vs 5 inward gaps). Bidirectional docs also force honest tracking of both consumption and contribution.

Consequences:
- 2 docs at root level instead of 1.
- Cross-reference audit (Phase 422) explicitly maps gaps to drafts.
- Future agents can choose direction without ambiguity.
- Prevents over-claiming the project's position relative to Mathlib.

References: `MATHLIB_GAPS.md`, `MATHLIB_PRS_OVERVIEW.md`, `LESSONS_LEARNED.md` §1.3, `CONTRIBUTING_FOR_AGENTS.md` §11.5.

---

## ADR-010 — Surface-doc propagation per arc
Status: accepted
Date: 2026-04-25 (Phases 411-413, 432-435, 440-442, 446-447, 462)

Decision:
Every major arc of work (e.g., L42 anchor block, L43 center symmetry, Mathlib upstream) is followed by a **propagation phase** that pushes its content into the canonical surface docs:
- `BLOQUE4_LEAN_REALIZATION.md` (master narrative)
- `FINAL_HANDOFF.md` (TL;DR)
- `STATE_OF_THE_PROJECT.md` (snapshot)
- `COWORK_FINDINGS.md` (findings log)
- `NEXT_SESSION.md` (orientation)
- `SESSION_*_FINAL_REPORT.md` (synthesis)
- `README.md` (discoverability)

Reason:
An arc's value is only realised if surface docs reflect it. Without propagation, the arc's content is invisible to anyone landing on the project (the Findings log doesn't show it; the TL;DR doesn't show it; the master narrative is stale). One propagation phase per arc is a small budget for a large discoverability gain.

Consequences:
- Slightly more phases per arc (1-2 propagation phases on top of N substantive phases).
- Surface-doc consistency at session-end (every doc reflects current state).
- Cross-reference structure naturally emerges (each surface doc points to the relevant arc-specific doc).

References: `LESSONS_LEARNED.md` §1.4, `CONTRIBUTING_FOR_AGENTS.md` §11.4.

---

## ADR-011 — Honest metric tracking (structural ≠ substantive)
Status: accepted
Date: 2026-04-25 (validated by Phases 403-465 producing extensive structural output without metric advance)

Decision:
The project's primary progress metric is **strict-Clay incondicional %**, defined as the percentage of named frontier entries (`AXIOM_FRONTIER.md` + `SORRY_FRONTIER.md`) retired. Structural / synthetic / contextual work (PR-ready files, anchor blocks, surface docs, findings) is **valuable but not metric-tracked**.

Reason:
Conflating structural with substantive work would create misleading progress signals. The 2026-04-25 session produced 38 Lean blocks + 18 PR-ready files + 22 surface docs (huge structural output), but the strict-Clay incondicional metric advanced only from ~12% to ~32% in the L30-L41 attack programme (Phases 283-402). Phases 403-465 (~63 phases) advanced the metric by 0%.

Consequences:
- Descriptions of session output explicitly distinguish "structural" from "substantive".
- The metric remains a reliable forward indicator.
- New sessions can set explicit goals against the metric.
- Continuous "continúa!" prompting can produce arbitrary structural output without metric advance — and this is **honestly tracked** rather than obscured.

References: `LESSONS_LEARNED.md` §2.5, `MID_TERM_STATUS_REPORT.md` §9.4, `CONTRIBUTING_FOR_AGENTS.md` §11.6.
