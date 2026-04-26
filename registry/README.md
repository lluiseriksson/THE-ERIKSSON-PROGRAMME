# registry/ — POSSIBLY STALE

This folder contains the project's **early-phase node registry**
(March 2026), which was built around an L0–L8 layer organisation
and consumed by `scripts/validate_registry.py` for CI consistency
checks.

The registry has not been maintained as the project evolved into
its current ClayCore + F3 frontier organisation. As of 2026-04-25
(v1.89.0), the registry has the following discrepancies with
actual repo state:

- **`ai_context.yaml`**: claims `current_phase: "Phase 0 —
  Sanitation and architecture"` and `primary_focus_node: L0.1`.
  Both are **incorrect**: Phase 0 closed in early March 2026, and
  the current focus is the F3 frontier in `YangMills/ClayCore/`.

- **`nodes.yaml`**: 29 nodes registered, last updated
  2026-04-01. Covers L0–L8 layers but **does NOT reflect**:
  - The ~275 files in `YangMills/ClayCore/` (the active work area)
  - The L2.4–L2.6 sidecar work (closed 2026-04-21/22)
  - The F3 frontier and its packaging (v1.79.0–v1.89.0)
  - The N_c=1 unconditional witness (`AbelianU1Unconditional.lean`)

- **`critical_paths.yaml`**: 3 paths defined entirely in terms of
  L0–L8 nodes. **Does not represent** the F3 frontier as the
  active critical path.

- **`bottlenecks.yaml`**: 7 bottlenecks. B01 (Kotecký–Preiss
  theorem) is the F3-Count work currently in progress; the rest
  are mostly historical or BLACKBOX outside scope.

- **`mathlib_blockers.yaml`**: M01 (finite-product Haar
  integration) was likely **resolved** by current L1 infrastructure
  but registry not updated.

For the **current critical-path organisation**, see (in order):

1. `FINAL_HANDOFF.md` (repo root) — 60-second TL;DR
2. `STATE_OF_THE_PROJECT.md` — current snapshot
3. `F3_CHAIN_MAP.md` — definitive F3 dependency graph (replaces
   the old L0–L8 critical paths for the active frontier)
4. `CODEX_CONSTRAINT_CONTRACT.md` §4 — current priority queue
5. `BLUEPRINT_F3Count.md` and `BLUEPRINT_F3Mayer.md` — the
   substantive analytic targets

The registry is preserved for git-history reference and for
potential future reuse. See `COWORK_FINDINGS.md` Finding 007 and
`REPO_INFRASTRUCTURE_AUDIT.md` §2 for the full discussion of the
dual-governance dead-weight situation and the proposed cleanup
options (Archive / Refresh / Defer).

---

## Note on `.github/workflows/ci.yml`

The CI configuration runs `scripts/validate_registry.py` against
this folder on every push. As long as the YAML structure is
internally consistent (which it is), CI passes — even though
the *content* is stale. CI is therefore not catching this
staleness; it's enforcing schema, not currency.

If `.github/workflows/ci.yml` is updated to remove the
`validate_registry` job (per Finding 007 Option A), the registry
folder can be safely archived or deleted without breaking CI.

---

*README added 2026-04-25 by Cowork agent as defensive staleness
flag pending Lluis decision per Finding 007.*
