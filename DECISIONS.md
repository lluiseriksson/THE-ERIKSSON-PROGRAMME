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
Status: accepted
Date: 2026-03-12

Decision:
The machine-readable registry under `registry/` is the canonical project state.

Reason:
Human summaries drift. AI sessions lose context. The registry must dominate.

Consequences:
- summaries must be generated from or checked against registry data
- contradictions must fail CI where possible

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
