# COWORK_RECOMMENDATIONS.md

Human-readable Cowork recommendation and audit log.

---

## 2026-04-26T07:30:00Z — AUDIT_PASS: COWORK-AUDIT-001 (whole coordination system)

**Audit result**: `AUDIT_PASS`. Whole agentic coordination system audited end-to-end. Task `COWORK-AUDIT-001` marked DONE. Baton handed to Codex with `CLAY-F3-COUNT-RECURSIVE-001`.

**Scope**: full coordination loop — `AGENT_BUS.md` COMMUNICATION_CONTRACT (13 clauses), `registry/agent_tasks.yaml`, `registry/recommendations.yaml`, `registry/agent_history.jsonl`, `dashboard/agent_state.json`, `scripts/agent_next_instruction.py`, `dashboard/codex_autocontinue_snapshot.py`, `dashboard/autocontinue_validation.txt`, `COWORK_RECOMMENDATIONS.md`, the new repeat-guard hardening Codex landed at 06:20:09Z and revalidated at 06:21:05Z.

**Five-dimension audit** (per task COWORK-AUDIT-001 objective):

| # | Dimension | Result | Evidence |
|---|---|---|---|
| 1 | Productive collaboration | PASS | History 58+ events showing dispatch / handoff / audit_pass ratchet. Tasks transition READY → IN_PROGRESS → DONE under task-rank discipline. Codex → Cowork → Codex baton flips visible. |
| 2 | Prevents generic continuation | PASS | Carry-over from COWORK-AUDIT-AUTOCONTINUE-001 (forbidden phrase absent in source, redacted in echo). |
| 3 | Records task history | PASS | `agent_history.jsonl` JSONL valid; `registry/agent_dispatch.lock` enforces atomic appends; one historical race-condition healed via `history_repair` event (visible at line 4). |
| 4 | Preserves future work | PASS | `META-GENERATE-TASKS-001` fallback fires when queue empties for an agent. Three fresh Clay-reduction READY tasks (`CLAY-F3-COUNT-RECURSIVE-001`, `CLAY-EXP-RETIRE-7-001`, `CLAY-MATHLIB-PR-LANDING-001`) seeded at 2026-04-26T07:00:00Z. Validation `≥ 3 Clay-reduction READY tasks` from `CLAY-ROADMAP-001` is therefore satisfied. |
| 5 | Anti-stale-loop hardening | PASS | **Layered defense verified**: (a) external watcher has hard wall-clock pauses keyed on `last_sent_task_id` — `REPEAT_TASK_PAUSE_SECONDS = 180.0`, `META_TASK_PAUSE_SECONDS = 1800.0` (snapshot lines 75-76); branches at lines 339-354 emit `[SKIP] {app.name}: Task id: {x} already sent; repeat guard active for {n}s.`. (b) canonical dispatcher applies soft `repeat_penalty` in `task_rank` order (line 605) — priority dominates so urgent re-dispatch is still possible. Two layers, one soft + one hard, structurally prevent the AGENTS.md §4 forbidden pattern "Two consecutive autocontinue dispatches of the same task without progress". |

**Bonus structural observation**: the layered defense is the right design. The watcher-side pause is a wall-clock guard, the dispatcher-side penalty is a rank-order guard. They use different signals (timestamp vs `last_dispatched_task` field), so they can't both fail to the same input. Defense in depth.

**Tasks updates**:
- `COWORK-AUDIT-001`: IN_PROGRESS → DONE with `audit_verdict: AUDIT_PASS` and 6 lines of evidence pointers in `audit_evidence:`.
- `CLAY-F3-COUNT-RECURSIVE-001`: remains READY priority 5, now the active baton for Codex.
- `CLAY-EXP-RETIRE-7-001`, `CLAY-MATHLIB-PR-LANDING-001`: remain READY in Codex queue.

**Ledger updates**:
- Row `AUTOCONTINUE`: INFRA_AUDITED confirmed (additional evidence: repeat-guard hardening pass).
- Row `AGENTIC-INFRA`: INFRA_AUDITED confirmed (system-wide audit including layered repeat defense).
- No mathematical row changed status. The `CLAY-GOAL` row remains BLOCKED. The lattice mass gap rows (`L1-HAAR`, `L2.4-SCHUR`, `L2.5-FROBENIUS`, `L2.6-CHARACTER`) remain at their FORMAL_KERNEL percentages. `F3-COUNT` remains CONDITIONAL_BRIDGE pending the recursive deletion / parent map.

**Honesty preservation**:
- The agentic infrastructure is now fully audited end-to-end. **This is meta-infrastructure progress, not Clay-level mathematical progress.**
- No claim about the Yang-Mills mass gap, the continuum limit, OS / Wightman reconstruction, or any Tier-1 row of `UNCONDITIONALITY_LEDGER.md` was made or accepted.
- The `claim_policy` in `dashboard/agent_state.json` is preserved: *"Never claim Clay-level completion without complete formal evidence."*

**No new recommendations filed.** No repair tasks created.

**Cowork-side observation for the human**: with the agentic infrastructure now AUDIT_PASS, the next 24/7 cycle should produce real Lean / Mathlib output rather than coordination metadata. The first Cowork audit milestone in the new regime is `COWORK-AUDIT-CLAY-F3-COUNT-RECURSIVE-001` (auto-create when Codex marks `CLAY-F3-COUNT-RECURSIVE-001` DONE with `lake build` + `#print axioms` evidence — see `AGENTS.md` §3.2 on auditable validation).

---

## 2026-04-26T07:00:00Z — AUDIT_PASS: COWORK-AUDIT-AUTOCONTINUE-001 (closes AUTOCONTINUE-001)

**Audit result**: `AUDIT_PASS`. AUTOCONTINUE-001 marked DONE. COWORK-AUDIT-AUTOCONTINUE-001 marked DONE. REC-AUDIT-AUTOCONTINUE-MIRROR-001 closed (RESOLVED). REC-BOOTSTRAP-001 closed (RESOLVED).

**Evidence reviewed**:

1. `dashboard/autocontinue_validation.txt` (159 lines) — literal stdout of all four commands:
   - `python C:\Users\lluis\Downloads\codex_autocontinue.py Codex`
   - `python C:\Users\lluis\Downloads\codex_autocontinue.py Cowork`
   - `python scripts\agent_next_instruction.py Codex`
   - `python scripts\agent_next_instruction.py Cowork`
2. `dashboard/codex_autocontinue_snapshot.py` (419 lines) — full snapshot of `C:\Users\lluis\Downloads\codex_autocontinue.py`.

**Seven-criterion audit** (per task COWORK-AUDIT-AUTOCONTINUE-001 objective):

| Criterion | Result | Evidence |
|---|---|---|
| (a) Structured dispatch | PASS | All 4 stdouts include task id, role, files to read, objective, validation, stop conditions, required updates, next exact instruction. |
| (b) History recorded | PASS | Watcher + CLI both delegate via `runpy` to `scripts/agent_next_instruction.py` whose history append is file-locked (`registry/agent_dispatch.lock`). |
| (c) Both roles supported | PASS | Snapshot line 407 `argparse` choices `["Codex", "Cowork"]`; line 171–172 raises on unknown role; watcher loads two `WatchedApp` instances. |
| (d) No generic continuation | PASS | The forbidden phrase string is **absent from the snapshot source** entirely. Where validation.txt echoes the AUTOCONTINUE-001 objective text it is rendered as `[forbidden generic phrase redacted]` — the dispatcher honours the forbidden-phrase rule even on echoed task descriptions. |
| (e) Future work preserved | PASS | `repo_codex` / `repo_cowork` sections (validation.txt lines 88–158) show `META-GENERATE-TASKS-001` dispatched with explicit instruction to create ≥ 3 new READY tasks when queue empties. |
| (f) Faithful mirror of canonical dispatcher | PASS (BETTER) | Snapshot lines 173–176: `runpy.run_path(str(CANONICAL_DISPATCHER))`, then `namespace["build_message"](agent_role)`. The script does **not** reimplement dispatcher logic — it loads it at runtime. **Silent divergence is structurally impossible**: only one source of truth (`scripts/agent_next_instruction.py`). |
| (g) Clay honesty | PASS | No overclaim phrases generated. Dispatcher only echoes `agent_tasks.yaml` fields. The `claim_policy` in `dashboard/agent_state.json` is preserved through every dispatch. |

**Bonus observations** (defensive engineering noted, no action required):

- Snapshot has FAILSAFE handling (lines 378–387), ghost-send detection (lines 354–364, prevents 1000 fake-clicks against an unfocused window), sanity bounds (line 48), pause/cooldown logic (lines 50–58), threshold-based ready/busy detection (lines 42–43, 232–235), and per-app calibration mode (lines 118–165).
- The `runpy` delegation pattern is the right architectural choice. It pays a tiny runtime cost (re-import the dispatcher per CLI call) but eliminates a whole class of audit bugs.

**Tasks created (Cowork-as-task-router, per CLAY-ROADMAP-001 §validation: "≥ 3 Clay-reduction tasks")**:

- `CLAY-F3-COUNT-RECURSIVE-001` (READY, owner Codex, priority 5) — F3 recursive deletion / parent map per AXIOM_FRONTIER v2.44.0. Active Clay-reduction frontier.
- `CLAY-EXP-RETIRE-7-001` (READY, owner Codex, priority 6) — retire 7 SU(N) generator-data Experimental axioms (~250 LOC, no Mathlib gap).
- `CLAY-MATHLIB-PR-LANDING-001` (READY, owner Codex, priority 7) — first Mathlib PR submission (`MatrixExp_DetTrace_DimOne_PR.lean`, closes literal Mathlib TODO).

**Ledger updates** (`UNCONDITIONALITY_LEDGER.md`):

- Row `AUTOCONTINUE` : `CONDITIONAL_BRIDGE` → `INFRA_AUDITED`. Evidence: `dashboard/autocontinue_validation.txt` + `dashboard/codex_autocontinue_snapshot.py` + the runpy-delegation invariant.
- Row `AGENTIC-INFRA` : `CONDITIONAL_BRIDGE` → `INFRA_AUDITED`. Bootstrap files in place, COMMUNICATION_CONTRACT 13 clauses active, AUTOCONTINUE audited.
- Row `CLAY-GOAL` : unchanged (`BLOCKED`). The agentic infrastructure is now sound; the Clay-reduction work itself begins under `CLAY-F3-COUNT-RECURSIVE-001`.

**Honesty preservation**:

- No row in `UNCONDITIONALITY_LEDGER.md` was upgraded to `FORMAL_KERNEL` outside the meta-infrastructure rows. The mathematical content is unchanged.
- No claim about Clay-level progress was made.
- The "ledger graduation" of AUTOCONTINUE / AGENTIC-INFRA is **infrastructure-only** — these rows exist to track the agentic system, not the Yang-Mills mathematics.

---

## 2026-04-26 — Audit entry: COMMUNICATION_CONTRACT bootstrap + AUTOCONTINUE-001 revert

**Audit result**: `AUDIT_PARTIAL` — in-repo dispatcher passes; Downloads-side autocontinue cannot be verified from this Cowork sandbox.

**Scope**: agentic-coordination infrastructure (AGENT_BUS, AGENTS, registry/, dashboard/, scripts/agent_next_instruction.py, claimed Downloads/codex_autocontinue.py update).

**Findings**:

1. **`scripts/agent_next_instruction.py` — PASS.**
   The canonical in-repo dispatcher exists with correct structure:
   `REPO_ROOT`, `TASKS_FILE`, `HISTORY_FILE`, `STATE_FILE`, `BUS_FILE`,
   `LOCK_FILE` constants; `VALID_AGENTS = {Codex, Cowork}`;
   `PRIMARY_STATUSES = {READY, PARTIAL}`, `FALLBACK_STATUSES = {IN_PROGRESS, FUTURE}`,
   `NEVER_DISPATCH = {DONE, CANCELLED, BLOCKED}`; `STALE_HOURS = 6`;
   lock-file based serialization for atomic JSONL appends. Complies with the
   COMMUNICATION_CONTRACT clauses 1, 3, 11.

2. **`registry/agent_history.jsonl` — PASS.**
   Append-only, JSONL valid, contains the `history_repair` event from the
   parallel-write race (good — Codex self-corrected with file-lock rather than
   silently overwriting). Demonstrates the system has self-healing properties.

3. **`AGENT_BUS.md` — PASS (post-bootstrap).**
   Now contains the `COMMUNICATION_CONTRACT` section with all 13 clauses
   from the human directive of 2026-04-26.

4. **`dashboard/agent_state.json` — PASS.**
   Schema valid (`project`, `strategic_goal`, `current_phase`,
   `current_baton_owner`, `next_task_id`, `last_completed_task`,
   `last_dispatched_task`, `last_dispatched_agent`, `open_blockers`,
   `open_recommendations`, `unconditionality_status`, `claim_policy`,
   `always_has_next_task`).

5. **`UNCONDITIONALITY_LEDGER.md` — PASS.**
   Status `NOT_ESTABLISHED`. Three-row ledger (CLAY-GOAL BLOCKED,
   AGENTIC-INFRA CONDITIONAL_BRIDGE, AUTOCONTINUE CONDITIONAL_BRIDGE).
   Honest. No overclaim.

6. **`C:\Users\lluis\Downloads\codex_autocontinue.py` — UNVERIFIABLE FROM SANDBOX.**
   Codex claimed DONE on 2026-04-26 with validation commands listed but no
   stdout transcript or file snapshot reachable from the Cowork sandbox.
   Per `AGENTS.md` §2 (done-criteria require auditable evidence) and §3.2
   ("I trust Codex" does NOT count as validation), the DONE claim cannot
   stand. **Reverted to `READY` priority 1.** See
   `REC-AUDIT-AUTOCONTINUE-MIRROR-001` in `registry/recommendations.yaml`.

**Repair task created**: `COWORK-AUDIT-AUTOCONTINUE-001` (FUTURE, owner Cowork; auto-activates when Codex provides Cowork-readable evidence — see recommendation REC-AUDIT-AUTOCONTINUE-MIRROR-001).

**Recommendations added**: 1 (`REC-AUDIT-AUTOCONTINUE-MIRROR-001`).

**Mathematical-honesty status**: unchanged. No row in `UNCONDITIONALITY_LEDGER.md` was upgraded to `FORMAL_KERNEL`. No claim about Clay-level progress was made or accepted. The two existing caveats (NC1-WITNESS vacuous, CONTINUUM-COORDSCALE not genuine continuum) remain on the surface in `KNOWN_ISSUES.md`.

**Cowork session impact**: infrastructure-only. Zero Lean files modified.

---

## REC-AUDIT-AUTOCONTINUE-MIRROR-001 (open)

Status: OPEN
Author: Cowork
Priority: 1
Converts to task: `AUTOCONTINUE-001` (modified) + `COWORK-AUDIT-AUTOCONTINUE-001`

Codex must dump the literal stdout of
`python C:\Users\lluis\Downloads\codex_autocontinue.py Codex` and `… Cowork`
to `dashboard/autocontinue_validation.txt`, plus the full contents of
`C:\Users\lluis\Downloads\codex_autocontinue.py` to
`dashboard/codex_autocontinue_snapshot.py`. Cowork will diff the snapshot
against `scripts/agent_next_instruction.py` to detect silent divergence.

---

## REC-BOOTSTRAP-001 (closed by REC-AUDIT-AUTOCONTINUE-MIRROR-001)

Status: SUPERSEDED-BY-REC-AUDIT-AUTOCONTINUE-MIRROR-001

Recommendation: Replace generic continuation with structured task dispatch
from `registry/agent_tasks.yaml`, with history and dashboard updates.

Reason: The project needs persistent auditability and task control for long-term
Clay-level formalization work.

Resolution note: in-repo dispatcher delivered; Downloads-side dispatcher
delivery is now tracked under `REC-AUDIT-AUTOCONTINUE-MIRROR-001`.
