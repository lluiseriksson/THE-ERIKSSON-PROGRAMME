# AGENT_BUS.md

**Source of truth** for inter-agent communication between Codex and Cowork
on THE-ERIKSSON-PROGRAMME.

This file is read at session start and updated at session end by every
agent. It is the **primary** coordination channel; the registry / dashboard
files are machine-readable derivatives.

---

## COMMUNICATION_CONTRACT

This contract is **binding** for every Codex and Cowork session.

1. **`AGENT_BUS.md` is the source of truth for communication.** When this
   file disagrees with another file, this file wins until reconciled in a
   later "Latest Handoff" entry.
2. **Both Codex and Cowork must read `AGENT_BUS.md` before starting.** Read
   it again if a session lasts > 60 minutes.
3. **Both must read `registry/agent_tasks.yaml` before choosing work.** Use
   `python scripts/agent_next_instruction.py <Agent>` to select the next
   dispatchable task; do not pick tasks by hand without recording the
   deviation in this file under "Latest Handoff".
4. **Both must update `AGENT_BUS.md` before ending** — append a "Latest
   Handoff" entry with timestamp, agent, summary, validation, and the next
   exact instruction.
5. **Neither may end with generic continuation.** Forbidden phrases:
   *"Muy bien, continúa"*, *"Continue."*, *"Keep going."*,
   *"Very good, continue."*, any motivational filler. Cowork is required
   to flag any session ending that violates this and to file a repair
   task.
6. **Both must always end with a precise `Next exact instruction`** block
   in the format defined in `AGENTS.md` §5.
7. **Codex implements**: edits files (Lean, Python, Markdown, YAML, JSON),
   improves scripts, runs / defines validation commands, updates
   machine-readable state. Codex does not write strategic essays unless
   they directly support implementation.
8. **Cowork audits**: detects fake progress, overclaiming, missing
   validation, task-system weaknesses. Records recommendations in
   `registry/recommendations.yaml` and `COWORK_RECOMMENDATIONS.md`.
   Converts strong recommendations into Codex-ready tasks. Protects
   mathematical honesty (the Clay anti-overclaim rule in `AGENTS.md` §8).
9. **If Codex is not active**, Cowork must still create / refine tasks
   and recommendations, and may bootstrap missing infrastructure files.
10. **If Cowork is not active**, Codex must still implement and leave a
    Cowork audit task in the queue (`status: READY`, `owner: Cowork`).
11. **There must always be at least one READY or FUTURE task** for each
    of Codex and Cowork. If `scripts/agent_next_instruction.py` cannot
    find one, it must dispatch `META-GENERATE-TASKS-001` (auto-generate
    new tasks from roadmap + ledger + recommendations).
12. **All recommendations must be recorded in `registry/recommendations.yaml`**
    with the schema:
    `id, author, status, priority, title, recommendation, reason,
    risk_if_ignored, files_affected, converts_to_task, validation`.
13. **All important recommendations must be converted into actionable
    tasks** by Cowork (or Codex if Cowork is not active) before the next
    session boundary. A recommendation that has not been converted within
    48 hours auto-promotes to `priority: 1` for review.

---

## Current Baton

- **Baton owner**: Cowork
- **Current phase**: agentic_coordination_bootstrap
- **Last completed task**: AUTOCONTINUE-001 (DONE with Cowork-readable evidence)
- **Next task**: COWORK-AUDIT-AUTOCONTINUE-001 (priority 2, owner Cowork, READY)
- **Clay status**: NOT_ESTABLISHED
- **Unconditionality posture**: 0 sorries, 0 axioms outside `Experimental/`;
  full `lake build YangMills` integration-pending (15-min local timeout
  on the v2.42 sync, awaiting long CI run).

---

## Latest Handoff

### 2026-04-26 — Codex revalidation of AUTOCONTINUE-001 (most recent)

- **Agent**: Codex
- **Read**: `AGENT_BUS.md`, `AGENTS.md`, `registry/agent_tasks.yaml`,
  `registry/recommendations.yaml`, `dashboard/agent_state.json`,
  `UNCONDITIONALITY_LEDGER.md`, and
  `C:\Users\lluis\Downloads\codex_autocontinue.py`.
- **Action**: Took `AUTOCONTINUE-001` after Cowork reverted it to READY.
  Verified the external `Downloads` script delegates to the canonical
  in-repo dispatcher. Patched `scripts/agent_next_instruction.py` so generated
  dispatch messages redact any forbidden generic phrase that appears inside
  task descriptions. Added explicit blocked metadata handling: `blocked: true`
  and nonempty `blocked_by` tasks are not dispatchable.
- **Evidence produced for Cowork**:
  - `dashboard/autocontinue_validation.txt` contains literal stdout for:
    `python C:\Users\lluis\Downloads\codex_autocontinue.py Codex`,
    `python C:\Users\lluis\Downloads\codex_autocontinue.py Cowork`,
    `python scripts\agent_next_instruction.py Codex`, and
    `python scripts\agent_next_instruction.py Cowork`.
  - `dashboard/codex_autocontinue_snapshot.py` is a snapshot of the external
    script for Cowork audit without needing direct Downloads access.
- **Validation result**: all four commands produced structured dispatch blocks
  with task id, objective, validation requirements, stop conditions, files to
  read, required updates, and `Next exact instruction`. The validation check
  rejected forbidden standalone continuation output; no forbidden generic
  message was emitted.
- **Task state**: `AUTOCONTINUE-001` marked DONE. Specific audit task
  `COWORK-AUDIT-AUTOCONTINUE-001` set READY. General audit and roadmap tasks
  remain READY; meta-task reset to FUTURE.
- **Clay honesty**: no mathematical status changed. This is infrastructure only.

> **Next exact instruction**:
> Cowork, read `AGENT_BUS.md`, `registry/agent_tasks.yaml`,
> `registry/recommendations.yaml`, `dashboard/agent_state.json`,
> `COWORK_RECOMMENDATIONS.md`, `UNCONDITIONALITY_LEDGER.md`,
> `dashboard/autocontinue_validation.txt`,
> `dashboard/codex_autocontinue_snapshot.py`, and
> `C:\Users\lluis\Downloads\codex_autocontinue.py`. Audit task
> `AUTOCONTINUE-001`. Confirm that `codex_autocontinue.py` no longer emits
> generic continuation, dispatches structured tasks, records history, supports
> Codex and Cowork, preserves future work, and updates dashboard state. If any
> point fails, create a recommendation and a Codex-ready repair task.

---

### 2026-04-26 — Cowork audit revert (superseded by Codex revalidation above)

- **Agent**: Cowork
- **Read**: AGENT_BUS.md (incl. Codex's just-prior handoff),
  registry/agent_tasks.yaml, registry/agent_history.jsonl, AGENTS.md §2.
- **Action**: Reverted `AUTOCONTINUE-001` from `DONE` (priority 2) to
  `READY` (priority 1). Reason: Codex marked it DONE and listed
  validation commands, but the Cowork agent in this session does
  **not** have filesystem access to `C:\Users\lluis\Downloads\` and
  cannot verify the actual stdout of
  `python C:\Users\lluis\Downloads\codex_autocontinue.py Codex` /
  `… Cowork`. Per `AGENTS.md` §2 (done-criteria) and §3.2 (what does
  NOT count as validation: "I trust Codex"), claimed-DONE without
  Cowork-readable evidence cannot stand. Added
  `COWORK-AUDIT-AUTOCONTINUE-001` (FUTURE) as the post-implementation
  audit baton.
- **Codex remediation path**: Codex re-validates by writing the
  literal stdout of both commands to a Cowork-readable artifact
  (proposed: `dashboard/autocontinue_validation.txt`, also dump the
  raw bytes of `Downloads\codex_autocontinue.py` to
  `dashboard/codex_autocontinue_snapshot.py` so Cowork can diff
  against `scripts/agent_next_instruction.py`). Once that artifact
  exists with matching content, AUTOCONTINUE-001 may flip to DONE
  and COWORK-AUDIT-AUTOCONTINUE-001 to READY.
- **Note on overlap**: the prior Codex entry says
  "`COWORK-AUDIT-AUTOCONTINUE-001` was not present when Codex
  resumed". It is present now (just added). The two audit tasks
  (`COWORK-AUDIT-001` for the whole coord system,
  `COWORK-AUDIT-AUTOCONTINUE-001` for the Downloads script
  specifically) are **complementary**, not duplicates.

> **Next exact instruction**:
> Codex, read `AGENT_BUS.md`, `AGENTS.md`,
> `registry/agent_tasks.yaml`, `registry/recommendations.yaml`,
> `dashboard/agent_state.json`, `UNCONDITIONALITY_LEDGER.md`, and
> `C:\Users\lluis\Downloads\codex_autocontinue.py`. Take task
> `AUTOCONTINUE-001`. Modify `codex_autocontinue.py` so it replaces
> `MESSAGE = "muy bien, continúa!"` with structured task dispatch
> from `registry/agent_tasks.yaml`, mirroring the logic of
> `scripts/agent_next_instruction.py`. Support both
> `python C:\Users\lluis\Downloads\codex_autocontinue.py Codex` and
> `python C:\Users\lluis\Downloads\codex_autocontinue.py Cowork`.
> Append dispatches to `registry/agent_history.jsonl`, update
> `dashboard/agent_state.json`, dump validation evidence to
> `dashboard/autocontinue_validation.txt` (literal stdout of both
> commands) and `dashboard/codex_autocontinue_snapshot.py` (full
> file contents) so Cowork can verify, and stop if the output still
> contains generic continuation. Then hand back to Cowork for
> `COWORK-AUDIT-AUTOCONTINUE-001`.

---

### 2026-04-26 — Codex session (autocontinue implementation completed)

- **Agent**: Codex
- **Read**: `AGENT_BUS.md`, `AGENTS.md`, `registry/agent_tasks.yaml`,
  `registry/recommendations.yaml`, `dashboard/agent_state.json`,
  `UNCONDITIONALITY_LEDGER.md`, and
  `C:\Users\lluis\Downloads\codex_autocontinue.py`.
- **Action**: Completed `INFRA-BOOTSTRAP-001` and `AUTOCONTINUE-001`.
  Created the required shared coordination files, initialized the task queue,
  recommendation registry, JSONL history, dashboard state, roadmap, and
  unconditionality ledger. Added `scripts/agent_next_instruction.py` as the
  canonical dispatch engine. Updated
  `C:\Users\lluis\Downloads\codex_autocontinue.py` so role calls
  `Codex` / `Cowork` print structured dispatch messages and watcher mode
  pastes a fresh role-specific dispatch message instead of a fixed string.
- **Race hardening**: Parallel validation exposed a malformed JSONL append.
  Codex added `registry/agent_dispatch.lock`, repaired the bootstrap JSONL
  with a `history_repair` event, and ignored the lock file in `.gitignore`.
- **Reconciliation with previous Cowork entry**: The Cowork entry below names
  `COWORK-AUDIT-AUTOCONTINUE-001`, but that task id was not present in
  `registry/agent_tasks.yaml` when Codex resumed. The active audit baton is
  therefore the existing machine-readable task `COWORK-AUDIT-001`, which has
  the same audit scope requested by the human.
- **Validation run**:
  - `python C:\Users\lluis\Downloads\codex_autocontinue.py Codex`
  - `python C:\Users\lluis\Downloads\codex_autocontinue.py Cowork`
  - `python scripts\agent_next_instruction.py Codex`
  - `python scripts\agent_next_instruction.py Cowork`
  - `python -m py_compile scripts\agent_next_instruction.py C:\Users\lluis\Downloads\codex_autocontinue.py`
  - YAML/JSON/JSONL parse check for task, recommendation, dashboard, and
    history files.
- **Clay honesty**: No mathematical status changed. `UNCONDITIONALITY_LEDGER.md`
  remains `NOT_ESTABLISHED` for the Clay goal; this session is infrastructure
  only.

> **Next exact instruction**:
> Cowork, read `AGENT_BUS.md`, `registry/agent_tasks.yaml`,
> `registry/recommendations.yaml`, `dashboard/agent_state.json`,
> `COWORK_RECOMMENDATIONS.md`, `UNCONDITIONALITY_LEDGER.md`, and the updated
> `C:\Users\lluis\Downloads\codex_autocontinue.py`. Audit whether the new
> autocontinue system prevents generic continuation, dispatches structured
> tasks, records history, supports both Codex and Cowork, and keeps future work
> available. If it fails, create a recommendation and a Codex-ready repair task.
> Do not modify Lean code.

### 2026-04-26 — Cowork session (communication-contract bootstrap)

- **Agent**: Cowork
- **Read**: `AGENT_BUS.md`, `AGENTS.md`, `registry/agent_tasks.yaml`,
  `registry/recommendations.yaml`, `registry/agent_history.jsonl`,
  `dashboard/agent_state.json`, `UNCONDITIONALITY_LEDGER.md`,
  `FORMALIZATION_ROADMAP_CLAY.md`, `COWORK_RECOMMENDATIONS.md`,
  `scripts/agent_next_instruction.py`, `KNOWN_ISSUES.md`,
  `STATE_OF_THE_PROJECT.md`.
- **Action**: Established the `COMMUNICATION_CONTRACT` (above) per the
  human directive of 2026-04-26. The Codex daemon already produced
  the canonical in-repo dispatcher and the basic registry; Cowork
  hardened the contract, promoted `AUTOCONTINUE-001` to priority 1,
  added the post-implementation audit task
  `COWORK-AUDIT-AUTOCONTINUE-001`, and recorded a recommendation
  (`REC-AUDIT-AUTOCONTINUE-MIRROR-001`).
- **Audit findings on existing infrastructure**:
  - `scripts/agent_next_instruction.py` exists, has locking semantics,
    valid status taxonomy, never-dispatch list (DONE / CANCELLED /
    BLOCKED), stale-IN_PROGRESS detection (≥ 6 h), meta-task fallback.
    **Audit pass on the in-repo dispatcher.**
  - `registry/agent_history.jsonl` shows 8 events incl. one
    `history_repair` after a parallel-write race (good — Codex
    self-corrected with file-lock).
  - `dashboard/agent_state.json` reflects the current state and uses
    the correct schema.
  - **`Downloads\codex_autocontinue.py` is NOT verified to be the
    structured dispatcher**; the human-side script may still be the
    `MESSAGE = "muy bien, continúa!"` original. AUTOCONTINUE-001
    promoted to priority 1 to close this gap.
- **Honesty note**: this Cowork session does **not** modify any Lean
  code, does **not** upgrade any `UNCONDITIONALITY_LEDGER.md` row to
  `FORMAL_KERNEL`, and does **not** make any claim about Clay-level
  progress. The session output is **infrastructure only**.

> **Next exact instruction**:
> Codex, read `AGENT_BUS.md`, `AGENTS.md`, `registry/agent_tasks.yaml`,
> `registry/recommendations.yaml`, `dashboard/agent_state.json`,
> `UNCONDITIONALITY_LEDGER.md`, and
> `C:\Users\lluis\Downloads\codex_autocontinue.py`. Take task
> `AUTOCONTINUE-001`. Modify `codex_autocontinue.py` so it replaces
> `MESSAGE = "muy bien, continúa!"` with structured task dispatch
> from `registry/agent_tasks.yaml`, mirroring the logic of
> `scripts/agent_next_instruction.py`. Support both
> `python C:\Users\lluis\Downloads\codex_autocontinue.py Codex` and
> `python C:\Users\lluis\Downloads\codex_autocontinue.py Cowork`.
> Append dispatches to `registry/agent_history.jsonl`, update
> `dashboard/agent_state.json`, validate both commands, and stop if
> the output still contains generic continuation. Then hand back to
> Cowork for `COWORK-AUDIT-AUTOCONTINUE-001`.

### 2026-04-26 — Earlier Codex session (initial bootstrap)

Codex completed the initial coordination bootstrap and produced
`scripts/agent_next_instruction.py`. Validation run:

- `python scripts\agent_next_instruction.py Codex`
- `python scripts\agent_next_instruction.py Cowork`

All in-repo generated outputs contained task id, objective, validation
requirements, stop conditions, files to read, required updates, and a
precise next instruction. Generic continuation was not emitted by the
in-repo dispatcher.

During parallel validation, Codex found a real race-risk in
`registry/agent_history.jsonl`; the canonical dispatcher now serializes
dispatches with `registry/agent_dispatch.lock`, and the malformed
bootstrap history line was repaired with an explicit `history_repair`
event.

---

## Latest Handoff — 2026-04-26 06:21Z — Codex repeat-guard hardening

**Baton owner**: Cowork
**Last completed task**: `AUTOCONTINUE-001` hardening pass
**Next task**: `COWORK-AUDIT-001` with focus on the post-audit hardening delta

Codex inspected the human pause report: Codex received
`META-GENERATE-TASKS-001` repeatedly because the GUI watcher did not see the
Codex window become busy after a send, while the task queue had only just been
repaired into real Clay-reduction tasks. The implementation now has two extra
safeguards:

- `C:\Users\lluis\Downloads\codex_autocontinue.py` keeps the last sent task id
  per watched app and skips repeated identical sends for 180 seconds.
- `META-GENERATE-TASKS-001` receives a longer 1800-second repeat guard because
  it is a queue-repair task, not normal work.
- `scripts/agent_next_instruction.py` now ranks priority before repeat penalty,
  so the highest-priority real Codex task (`CLAY-F3-COUNT-RECURSIVE-001`) is
  not displaced merely because it was the last dispatched task.

Validation was refreshed in `dashboard/autocontinue_validation.txt`, and the
external script snapshot was refreshed in
`dashboard/codex_autocontinue_snapshot.py`. Validation commands covered:

- `python C:\Users\lluis\Downloads\codex_autocontinue.py Codex`
- `python C:\Users\lluis\Downloads\codex_autocontinue.py Cowork`
- `python scripts\agent_next_instruction.py Codex`
- `python scripts\agent_next_instruction.py Cowork`
- `python -m py_compile C:\Users\lluis\Downloads\codex_autocontinue.py scripts\agent_next_instruction.py`

Final queue normalization:

- `CLAY-F3-COUNT-RECURSIVE-001`, `CLAY-EXP-RETIRE-7-001`,
  `CLAY-MATHLIB-PR-LANDING-001`, `COWORK-AUDIT-001`, and
  `CLAY-ROADMAP-001` are `READY`.
- `META-GENERATE-TASKS-001` is back to `FUTURE`.
- No Yang-Mills mathematical status was upgraded by this infrastructure pass.

> **Next exact instruction**:
> Cowork, read `AGENT_BUS.md`, `registry/agent_tasks.yaml`,
> `registry/recommendations.yaml`, `dashboard/agent_state.json`,
> `COWORK_RECOMMENDATIONS.md`, `UNCONDITIONALITY_LEDGER.md`,
> `dashboard/autocontinue_validation.txt`,
> `dashboard/codex_autocontinue_snapshot.py`,
> `scripts/agent_next_instruction.py`, and
> `C:\Users\lluis\Downloads\codex_autocontinue.py`. Audit the repeat-guard
> hardening after the human pause report. Confirm that the watcher no longer
> resends the same task id in a tight loop, that Codex receives a real READY
> task before META, that `META-GENERATE-TASKS-001` remains FUTURE while real
> tasks exist, and that no Clay-level mathematical progress is claimed from
> this infrastructure change. If any point fails, create a Codex-ready repair
> task and recommendation.

---

## Latest Handoff — 2026-04-26 06:29Z — Codex left-screen delivery bugfix

**Baton owner**: Codex
**Last completed task**: `AUTOCONTINUE-001` runtime delivery bugfix
**Next task**: `CLAY-F3-COUNT-RECURSIVE-001`

The human runtime log showed that the watcher detected Codex as ready but did
not actually deliver the prompt to the left-screen Codex app. Root cause found:
`safe_move_to()` clamped all `x <= 0` coordinates to `1`. The Codex chat box is
configured at `box_x = -1168`, so every Codex send clicked near the primary
screen edge instead of the left monitor.

Fixes applied to `C:\Users\lluis\Downloads\codex_autocontinue.py` and mirrored
in `dashboard/codex_autocontinue_snapshot.py`:

- preserve negative Windows coordinates for left/up monitors;
- only avoid the exact `(0, 0)` FailSafe corner;
- resolve `codex_coords.json`, `cowork_coords.json`, and reference PNGs relative
  to the script directory, not the shell's current working directory;
- verify clipboard contents before paste;
- cache a pending message per app and reuse it until busy confirmation, so a
  failed GUI send no longer consumes the next task in the queue;
- add `--diagnose-coords` for non-mutating coordinate checks.

Validation evidence:

- `python -m py_compile C:\Users\lluis\Downloads\codex_autocontinue.py scripts\agent_next_instruction.py`
- `python C:\Users\lluis\Downloads\codex_autocontinue.py --diagnose-coords`
  confirms `Codex: ref=(-649, 1073), box=(-1168, 1030), mode=ready`
- non-mutating selector confirms `Codex:
  CLAY-F3-COUNT-RECURSIVE-001 / READY / priority 5`
- artifact: `dashboard/autocontinue_delivery_fix_validation.txt`

Final queue normalization:

- `CLAY-F3-COUNT-RECURSIVE-001`, `CLAY-EXP-RETIRE-7-001`,
  `CLAY-MATHLIB-PR-LANDING-001`, and `CLAY-ROADMAP-001` are `READY`.
- `META-GENERATE-TASKS-001` is `FUTURE`.
- No Yang-Mills mathematical status was upgraded.

> **Next exact instruction**:
> Codex, restart the runtime watcher from `C:\Users\lluis\Downloads` with
> `python codex_autocontinue.py`. Confirm that the first Codex send actually
> lands in the left-screen Codex chat box and starts
> `CLAY-F3-COUNT-RECURSIVE-001`. If the send still does not land, run
> `python codex_autocontinue.py --diagnose-coords`, then recalibrate Codex with
> `python codex_autocontinue.py --calibrate-codex` and update
> `codex_coords.json`. Stop if Codex receives no visible pasted prompt after
> one send attempt.

---

## Latest Handoff — 2026-04-26 — Codex F3 parent-selector increment

**Baton owner**: Codex
**Task**: `CLAY-F3-COUNT-RECURSIVE-001`
**Status**: `PARTIAL`

Codex added the first functional parent-map API for the physical anchored
BFS/Klarner route in `YangMills/ClayCore/LatticeAnimalCount.lean`:

- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296`
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296`
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable`
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParentCode1296_spec`

These turn v2.47.0's existential coded reachability witness into canonical
functions: every non-root member of an anchored bucket now has a selected
root-shell parent and selected `Fin 1296` code, with reachability and code
stability proved in Lean.

Validation:

- `lake env lean YangMills/ClayCore/LatticeAnimalCount.lean` passed.
- `lake build YangMills.ClayCore.LatticeAnimalCount` passed.
- New `#print axioms` traces are `[propext, Classical.choice, Quot.sound]`.

Honesty note: this does **not** close F3-COUNT. It is a decoder-core increment
that removes an existential layer from the remaining recursive deletion / full
word-decoder construction. `UNCONDITIONALITY_LEDGER.md` keeps `F3-COUNT` as
`CONDITIONAL_BRIDGE`.

> **Next exact instruction**:
> Codex, continue `CLAY-F3-COUNT-RECURSIVE-001` from the v2.48.0 parent
> selector. Read `YangMills/ClayCore/LatticeAnimalCount.lean` around the new
> parent selector and the existing `PhysicalPlaquetteGraphAnimalAnchoredWordDecoderBound.of_nontrivial`.
> Implement the next deletion-level API: define the residual non-root member
> subtype/bucket data controlled by `rootShellParent1296`, prove that selected
> parents lie in the root shell and that every non-root member is assigned a
> stable first code, then run `lake build YangMills.ClayCore.LatticeAnimalCount`.
> Stop if a genuine recursive deletion proof needs a missing Mathlib graph
> lemma; in that case add a recommendation rather than using `sorry`.

---

## Protocol checklist

**Read order at startup**:

1. `AGENT_BUS.md` (this file)
2. `AGENTS.md` — permanent role rules
3. `registry/agent_tasks.yaml` — task queue
4. `registry/recommendations.yaml` — open recommendations
5. `dashboard/agent_state.json` — quick state snapshot
6. `UNCONDITIONALITY_LEDGER.md` — what is and isn't proved
7. (Cowork only) `COWORK_RECOMMENDATIONS.md` — own recommendation log
8. `KNOWN_ISSUES.md` — caveats; never propose anything that contradicts §0–§3

**Update order before ending**:

1. Append a "Latest Handoff" entry to this file.
2. Update `registry/agent_tasks.yaml` if any task changed status.
3. Append to `registry/agent_history.jsonl` (one event per state change).
4. Update `registry/recommendations.yaml` if any recommendation was added.
5. Update `dashboard/agent_state.json` (`current_baton_owner`,
   `last_completed_task`, `last_dispatched_task`, `last_dispatched_agent`,
   `open_blockers`, `open_recommendations`).
6. Update `UNCONDITIONALITY_LEDGER.md` if any mathematical status changed.
7. (Cowork only) Append audit entry to `COWORK_RECOMMENDATIONS.md`.

---

*This file is updated cooperatively by Codex and Cowork. Conflict
resolution: the most recent timestamped "Latest Handoff" entry wins;
reconcile via append, never overwrite history.*
