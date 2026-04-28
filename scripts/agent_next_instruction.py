#!/usr/bin/env python3
"""Structured task dispatcher for Codex/Cowork collaboration.

This script is the canonical source for the autocontinue task-selection logic.
It initializes the shared coordination files, chooses the next actionable task
for Codex or Cowork, records the dispatch, updates the dashboard, and prints a
precise instruction block. It intentionally never emits generic encouragement.
"""

from __future__ import annotations

import json
import os
import re
import sys
import time
from copy import deepcopy
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    import yaml
except ImportError as exc:  # pragma: no cover - environment failure
    raise SystemExit("PyYAML is required for agent_next_instruction.py") from exc

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")


REPO_ROOT = Path(r"C:\Users\lluis\.gemini\antigravity\scratch\THE-ERIKSSON-PROGRAMME")
TASKS_FILE = REPO_ROOT / "registry" / "agent_tasks.yaml"
HISTORY_FILE = REPO_ROOT / "registry" / "agent_history.jsonl"
RECOMMENDATIONS_FILE = REPO_ROOT / "registry" / "recommendations.yaml"
STATE_FILE = REPO_ROOT / "dashboard" / "agent_state.json"
BUS_FILE = REPO_ROOT / "AGENT_BUS.md"
LOCK_FILE = REPO_ROOT / "registry" / "agent_dispatch.lock"
AGENTS_FILE = REPO_ROOT / "AGENTS.md"
COWORK_RECOMMENDATIONS_FILE = REPO_ROOT / "COWORK_RECOMMENDATIONS.md"
ROADMAP_FILE = REPO_ROOT / "FORMALIZATION_ROADMAP_CLAY.md"
LEDGER_FILE = REPO_ROOT / "UNCONDITIONALITY_LEDGER.md"
EXTERNAL_AUTOCONTINUE = Path(r"C:\Users\lluis\Downloads\codex_autocontinue.py")

VALID_AGENTS = {"Codex", "Cowork"}
PRIMARY_STATUSES = {"READY": 0, "PARTIAL": 1}
FALLBACK_STATUSES = {"IN_PROGRESS": 2, "FUTURE": 3}
NEVER_DISPATCH = {"DONE", "CANCELLED", "BLOCKED", "SUPERSEDED"}
COMPLETION_VERDICTS = {
    "AUDIT_PASS",
    "AUDIT_FAIL",
    "DELIVERED",
    "DONE",
    "RESOLVED",
    "CANCELLED",
}
STALE_HOURS = 6
GHOST_IN_PROGRESS_DIAGNOSTIC_SECONDS = 60
DIAGNOSTIC_STALE_UNCONFIRMED_HOURS = 24
RECENT_REPEAT_SUPPRESS_SECONDS = 300
LOCK_POLL_SECONDS = 0.1
LOCK_TIMEOUT_SECONDS = 30
CONFIRMED_DELIVERY_STATES = {"CONFIRMED_BUSY", "CONFIRMED_DELIVERY"}
UNCONFIRMED_DELIVERY_STATES = {
    "DISPATCH_MUTATED_PENDING_CONFIRMATION",
    "UNCONFIRMED_SEND_RETRY_PENDING",
    "ABANDONED_UNCONFIRMED",
    "QUARANTINED_UNCONFIRMED",
}
VERSIONED_COWORK_AUDIT = re.compile(r"^COWORK-AUDIT-CODEX-V(\d+(?:\.\d+)*)")
CODEX_TASK_ID_RE = re.compile(r"\bCODEX-[A-Z0-9][A-Z0-9._-]*-\d{3}\b")
COWORK_AUDIT_SUBSTRATE_WAIT_SECONDS = 15 * 60
COWORK_POLLING_TASK_PREFIXES = (
    "COWORK-LEDGER-FRESHNESS-AUDIT",
    "COWORK-DELIVERABLES-CONSISTENCY-AUDIT",
    "COWORK-DELIVERABLES-INDEX-REFRESH",
    "COWORK-AUDIT-FRESH-PERCENTAGE-MOVE",
    "COWORK-AUDIT-MATHLIB-PR-DRAFT-STATUS",
)
META_TASK_IDS = {"META-GENERATE-TASKS-001", "META-DISPATCHER-FAILSAFE-001"}


class YAMLRegistryError(RuntimeError):
    """Raised when a shared YAML registry cannot be parsed."""

    def __init__(self, path: Path, original: BaseException):
        self.path = path
        self.original = original
        super().__init__(f"{path}: {original}")


INITIAL_TASKS = [
    {
        "id": "INFRA-BOOTSTRAP-001",
        "title": "Create shared Codex/Cowork coordination files",
        "owner": "Codex",
        "status": "READY",
        "priority": 1,
        "created_at": "2026-04-26T00:00:00Z",
        "updated_at": "2026-04-26T00:00:00Z",
        "required_files": [
            "AGENTS.md",
            "AGENT_BUS.md",
            "UNCONDITIONALITY_LEDGER.md",
        ],
        "objective": (
            "Create the shared communication, task, recommendation, dashboard, "
            "roadmap, and unconditionality-ledger files required for Codex and "
            "Cowork to work synergistically."
        ),
        "validation": [
            "python scripts/agent_next_instruction.py Codex",
            "python scripts/agent_next_instruction.py Cowork",
        ],
        "stop_if": [
            "Cannot write files",
            "Existing project structure contradicts the coordination system",
        ],
        "next_agent": "Cowork",
        "notes": [],
    },
    {
        "id": "AUTOCONTINUE-001",
        "title": "Replace generic autocontinue message with structured task dispatch",
        "owner": "Codex",
        "status": "READY",
        "priority": 2,
        "created_at": "2026-04-26T00:00:00Z",
        "updated_at": "2026-04-26T00:00:00Z",
        "required_files": [
            str(EXTERNAL_AUTOCONTINUE),
            "registry/agent_tasks.yaml",
            "registry/agent_history.jsonl",
            "dashboard/agent_state.json",
            "AGENT_BUS.md",
        ],
        "objective": (
            "Modify codex_autocontinue.py so it no longer sends a generic "
            "continuation message. It must read structured tasks, dispatch the "
            "next useful task, update history, update dashboard state, and "
            "support Codex/Cowork roles."
        ),
        "validation": [
            f"python {EXTERNAL_AUTOCONTINUE} Codex",
            f"python {EXTERNAL_AUTOCONTINUE} Cowork",
        ],
        "stop_if": [
            "The script cannot access the repo path",
            "The generated message still contains generic continuation",
            "The task registry cannot be read or safely initialized",
        ],
        "next_agent": "Cowork",
        "notes": [],
    },
    {
        "id": "COWORK-AUDIT-001",
        "title": "Audit autocontinue and coordination system",
        "owner": "Cowork",
        "status": "READY",
        "priority": 3,
        "created_at": "2026-04-26T00:00:00Z",
        "updated_at": "2026-04-26T00:00:00Z",
        "required_files": [
            "AGENT_BUS.md",
            "registry/agent_tasks.yaml",
            "registry/recommendations.yaml",
            "dashboard/agent_state.json",
            "COWORK_RECOMMENDATIONS.md",
            str(EXTERNAL_AUTOCONTINUE),
        ],
        "objective": (
            "Audit whether the new system makes Codex and Cowork collaborate "
            "productively, prevents generic continuation, records task history, "
            "and always preserves useful future work."
        ),
        "validation": [
            "COWORK_RECOMMENDATIONS.md contains an audit entry",
            "registry/recommendations.yaml contains any required recommendations",
            "registry/agent_tasks.yaml contains repair tasks if issues are found",
        ],
        "stop_if": [
            "Codex did not create the required files",
            "The autocontinue script still sends generic messages",
        ],
        "next_agent": "Codex",
        "notes": [],
    },
    {
        "id": "CLAY-ROADMAP-001",
        "title": "Build and maintain Clay-level formalization roadmap",
        "owner": "Cowork",
        "status": "READY",
        "priority": 4,
        "created_at": "2026-04-26T00:00:00Z",
        "updated_at": "2026-04-26T00:00:00Z",
        "required_files": [
            "FORMALIZATION_ROADMAP_CLAY.md",
            "UNCONDITIONALITY_LEDGER.md",
            "registry/recommendations.yaml",
        ],
        "objective": (
            "Decompose the Clay-level Yang-Mills goal into formal milestones, "
            "assumptions, bridges, blockers, and Codex-ready implementation "
            "tasks."
        ),
        "validation": [
            "FORMALIZATION_ROADMAP_CLAY.md contains milestone sections",
            "UNCONDITIONALITY_LEDGER.md tracks all conditional dependencies",
            "registry/agent_tasks.yaml contains at least three Clay-reduction tasks",
        ],
        "stop_if": [
            "Any section claims the Clay problem is solved without formal evidence",
        ],
        "next_agent": "Codex",
        "notes": [],
    },
    {
        "id": "META-GENERATE-TASKS-001",
        "title": "Generate new actionable tasks when the queue is empty",
        "owner": "Any",
        "status": "FUTURE",
        "priority": 99,
        "created_at": "2026-04-26T00:00:00Z",
        "updated_at": "2026-04-26T00:00:00Z",
        "required_files": [
            "AGENT_BUS.md",
            "FORMALIZATION_ROADMAP_CLAY.md",
            "UNCONDITIONALITY_LEDGER.md",
            "registry/recommendations.yaml",
            "registry/agent_tasks.yaml",
        ],
        "objective": (
            "If no READY or PARTIAL tasks exist, inspect the roadmap, ledger, "
            "recommendations, and current state, then create at least three new "
            "READY tasks that advance the project."
        ),
        "validation": [
            "registry/agent_tasks.yaml contains at least three READY tasks",
        ],
        "stop_if": [
            "Roadmap and ledger are missing",
        ],
        "next_agent": "Codex",
        "notes": [],
    },
]


INITIAL_RECOMMENDATIONS = [
    {
        "id": "REC-BOOTSTRAP-001",
        "author": "Human",
        "status": "OPEN",
        "priority": 1,
        "title": "Replace generic continuation with structured task dispatch",
        "recommendation": (
            "The autocontinue system must dispatch precise structured tasks from "
            "a shared registry instead of sending generic encouragement."
        ),
        "reason": (
            "A five-year Clay-level research programme requires persistent task "
            "control, auditability, and agent coordination."
        ),
        "risk_if_ignored": (
            "Agents may remain active 24/7 while making little or no real progress."
        ),
        "files_affected": [
            str(EXTERNAL_AUTOCONTINUE),
            "registry/agent_tasks.yaml",
            "registry/agent_history.jsonl",
            "dashboard/agent_state.json",
        ],
        "converts_to_task": "AUTOCONTINUE-001",
        "validation": (
            "Running the autocontinue script for both Codex and Cowork produces "
            "precise task instructions and never emits generic continuation."
        ),
    }
]


INITIAL_STATE = {
    "project": "THE-ERIKSSON-PROGRAMME",
    "strategic_goal": (
        "Five-year day-by-day progress toward unconditional Clay-level "
        "Yang-Mills Mass Gap formalization"
    ),
    "current_phase": "agentic_coordination_bootstrap",
    "current_baton_owner": "Codex",
    "next_task_id": "INFRA-BOOTSTRAP-001",
    "last_completed_task": None,
    "last_dispatched_task": None,
    "last_dispatched_agent": None,
    "open_blockers": [],
    "open_recommendations": ["REC-BOOTSTRAP-001"],
    "unconditionality_status": "NOT_ESTABLISHED",
    "claim_policy": "Never claim Clay-level completion without complete formal evidence.",
    "always_has_next_task": True,
}


TEXT_DEFAULTS = {
    AGENTS_FILE: """# AGENTS.md

Permanent operating rules for THE-ERIKSSON-PROGRAMME agents.

## Mission

Build a rigorous, auditable, continuously improving research and formalization
system aimed at reducing conditionality toward a Clay-level Yang-Mills Mass Gap
proof. The Clay problem remains unsolved unless the repository contains a
complete verified unconditional formal chain and dependency ledger.

## Roles

### Codex
- Implementation and automation agent.
- Creates files, scripts, Lean infrastructure, registries, and validation.
- Converts vague goals into executable tasks.
- Must update task, history, dashboard, and bus files before handoff.

### Cowork
- Strategy, audit, recommendation, and mathematical-honesty agent.
- Audits Codex changes, detects fake progress, records recommendations, and
  turns strong recommendations into Codex-ready tasks.
- Does not implement production code unless explicitly instructed.

## Validation Policy

Every task must list validation commands or concrete audit criteria. A task is
not DONE until those validations are run or the reason they could not be run is
recorded.

## Done Criteria

A cycle is done only when:
- relevant files are updated,
- task state is recorded,
- dispatch/history/dashboard are consistent,
- no Clay-level completion claim is made without formal evidence,
- the final handoff contains a precise Next exact instruction.

## Forbidden Endings

Agents must never end with generic continuation or motivational filler. Every
cycle must end with a specific next agent, files to read, task id, validation,
and stop condition.
""",
    BUS_FILE: """# AGENT_BUS.md

Shared communication channel for Codex and Cowork.

## Current Baton

- Baton owner: Codex
- Current phase: agentic_coordination_bootstrap
- Current task: INFRA-BOOTSTRAP-001 / AUTOCONTINUE-001
- Clay status: NOT_ESTABLISHED

## Protocol

1. Read this file, `registry/agent_tasks.yaml`, `registry/recommendations.yaml`,
   `dashboard/agent_state.json`, and `UNCONDITIONALITY_LEDGER.md` at startup.
2. Work one concrete task at a time.
3. Update task status, history, dashboard, and this bus before ending.
4. Leave a precise Next exact instruction.

## Latest Handoff

Codex is bootstrapping the coordination system and replacing generic
autocontinue messages with structured task dispatch.
""",
    COWORK_RECOMMENDATIONS_FILE: """# COWORK_RECOMMENDATIONS.md

Human-readable Cowork recommendation and audit log.

## REC-BOOTSTRAP-001

Status: OPEN

Recommendation: Replace generic continuation with structured task dispatch
from `registry/agent_tasks.yaml`, with history and dashboard updates.

Reason: The project needs persistent auditability and task control for long-term
Clay-level formalization work.
""",
    ROADMAP_FILE: """# FORMALIZATION_ROADMAP_CLAY.md

## Purpose

This roadmap decomposes the five-year Clay-level Yang-Mills objective into daily
actionable formalization, audit, and research tasks.

## Strategic target

Reach a fully unconditional formal proof chain for the Clay Yang-Mills Mass Gap
problem.

## Non-negotiable rule

This roadmap is not a proof. It is a dependency map. No item is complete until
the corresponding formal, audit, and ledger evidence exists.

## Milestones

### M0 - Agentic research infrastructure
- Codex/Cowork coordination
- task queue
- recommendation registry
- history log
- audit loop
- no generic continuation

### M1 - Formal honesty and dependency control
- unconditionality ledger
- allowed foundations
- forbidden assumptions
- proof-status taxonomy
- blocker registry

### M2 - Classical Yang-Mills geometry
- compact simple gauge groups
- bundles
- connections
- curvature
- Yang-Mills action
- gauge transformations
- classical equations

### M3 - Euclidean constructive layer
- regularization
- lattice/continuum bridge
- measures
- reflection positivity
- Schwinger functions
- correlation decay

### M4 - OS/Wightman reconstruction
- OS axioms
- Hilbert space reconstruction
- locality
- covariance
- spectral condition
- nontriviality

### M5 - Mass gap
- formal definition of mass gap
- spectral lower bound
- relation to correlation decay
- positivity of Delta

### M6 - Unconditionality closure
- remove conditional bridges
- prove or eliminate assumptions
- audit all dependencies
- align final theorem with Clay statement

## Daily work rule

Every day's work must reduce at least one of:
- ambiguity
- missing formal definition
- missing theorem
- conditional bridge
- untracked assumption
- unvalidated script
- agent coordination weakness
""",
    LEDGER_FILE: """# UNCONDITIONALITY_LEDGER.md

This ledger tracks every assumption, bridge, axiom, placeholder, conditional
theorem, experimental result, and unresolved blocker.

## Global Clay status

Status:
- NOT_ESTABLISHED

Reason:
- The repository does not yet contain a complete unconditional formal proof of
  the Clay Yang-Mills Mass Gap problem.

## Status labels

- FORMAL_KERNEL: verified by Lean without project-specific assumptions
- MATHLIB_FOUNDATIONAL: depends only on accepted Lean/Mathlib foundations
- CONDITIONAL_BRIDGE: depends on an explicitly stated unproved mathematical bridge
- EXPERIMENTAL: exploratory and not part of the proof chain
- HEURISTIC: motivational or strategic only
- BLOCKED: cannot progress without a theorem, definition, or decision
- INVALID: must not be used

## Ledger

| ID | Claim | Status | Dependency | Evidence | Next action |
|---|---|---|---|---|---|
| CLAY-GOAL | Full Clay-level Yang-Mills existence and mass gap | BLOCKED | Complete formal chain | FORMALIZATION_ROADMAP_CLAY.md | Decompose into milestones |
| AGENTIC-INFRA | Codex/Cowork coordination system | CONDITIONAL_BRIDGE | Bootstrap files and audit | AGENT_BUS.md | Codex creates, Cowork audits |
| AUTOCONTINUE | 24/7 task dispatch system | CONDITIONAL_BRIDGE | codex_autocontinue.py | registry/agent_tasks.yaml | Replace generic message with structured task dispatch |
""",
}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


@contextmanager
def coordination_lock():
    """Serialize task/dashboard/history updates across concurrent agents."""
    LOCK_FILE.parent.mkdir(parents=True, exist_ok=True)
    if os.name == "nt":
        import msvcrt

        with LOCK_FILE.open("a+b") as handle:
            deadline = time.time() + LOCK_TIMEOUT_SECONDS
            while True:
                try:
                    handle.seek(0)
                    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                    break
                except OSError:
                    if time.time() > deadline:
                        raise TimeoutError(f"Timed out waiting for dispatch lock: {LOCK_FILE}")
                    time.sleep(LOCK_POLL_SECONDS)
            try:
                yield
            finally:
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
    else:
        import fcntl

        with LOCK_FILE.open("a+b") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def load_yaml(path: Path) -> dict[str, Any]:
    if not path.exists() or path.read_text(encoding="utf-8").strip() == "":
        return {}
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except yaml.YAMLError as exc:
        raise YAMLRegistryError(path, exc) from exc
    return data if isinstance(data, dict) else {}


def save_yaml(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True), encoding="utf-8")


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists() or path.read_text(encoding="utf-8").strip() == "":
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def save_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def append_history(event: dict[str, Any]) -> None:
    HISTORY_FILE.parent.mkdir(parents=True, exist_ok=True)
    with HISTORY_FILE.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(event, ensure_ascii=False, sort_keys=True) + "\n")


def merge_by_id(existing: list[dict[str, Any]], defaults: list[dict[str, Any]]) -> list[dict[str, Any]]:
    items = [deepcopy(item) for item in existing if isinstance(item, dict)]
    seen = {item.get("id") for item in items}
    for default in defaults:
        if default["id"] not in seen:
            items.append(deepcopy(default))
            seen.add(default["id"])
    return items


def ensure_base_files() -> None:
    (REPO_ROOT / "registry").mkdir(parents=True, exist_ok=True)
    (REPO_ROOT / "dashboard").mkdir(parents=True, exist_ok=True)
    (REPO_ROOT / "scripts").mkdir(parents=True, exist_ok=True)

    tasks_doc = load_yaml(TASKS_FILE)
    tasks_doc["tasks"] = merge_by_id(tasks_doc.get("tasks", []), INITIAL_TASKS)
    save_yaml(TASKS_FILE, tasks_doc)

    recs_doc = load_yaml(RECOMMENDATIONS_FILE)
    recs_doc["recommendations"] = merge_by_id(
        recs_doc.get("recommendations", []), INITIAL_RECOMMENDATIONS
    )
    save_yaml(RECOMMENDATIONS_FILE, recs_doc)

    if not HISTORY_FILE.exists():
        HISTORY_FILE.write_text("", encoding="utf-8")

    state = INITIAL_STATE | load_json(STATE_FILE)
    state.setdefault("open_recommendations", ["REC-BOOTSTRAP-001"])
    save_json(STATE_FILE, state)

    for path, content in TEXT_DEFAULTS.items():
        if not path.exists() or path.read_text(encoding="utf-8", errors="ignore").strip() == "":
            path.write_text(content, encoding="utf-8")


def parse_time(value: Any) -> datetime:
    if not isinstance(value, str):
        return datetime.min.replace(tzinfo=timezone.utc)
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return datetime.min.replace(tzinfo=timezone.utc)


def task_age_seconds(task: dict[str, Any]) -> float:
    updated = parse_time(task.get("dispatched_at") or task.get("updated_at"))
    return (datetime.now(timezone.utc) - updated).total_seconds()


def delivery_state(task: dict[str, Any]) -> str:
    return str(task.get("delivery_state", "")).upper()


def dispatch_confirmed(task: dict[str, Any]) -> bool:
    return bool(task.get("delivery_confirmed_at")) or delivery_state(task) in CONFIRMED_DELIVERY_STATES


def has_completion_evidence(task: dict[str, Any]) -> bool:
    if task.get("completed_at") or task.get("result"):
        return True
    verdict = str(task.get("audit_verdict", "")).upper()
    if verdict in COMPLETION_VERDICTS:
        return True
    return bool(task.get("delivery_artifact") or task.get("deliverable"))


def is_stale(task: dict[str, Any]) -> bool:
    if task.get("status") != "IN_PROGRESS":
        return False
    if not dispatch_confirmed(task):
        return False
    return task_age_seconds(task) >= STALE_HOURS * 3600


def is_blocked(task: dict[str, Any]) -> bool:
    """Treat explicit blocked metadata as non-dispatchable."""
    if task.get("blocked") is True:
        return True
    blocked_by = task.get("blocked_by")
    if isinstance(blocked_by, list) and blocked_by:
        return True
    if isinstance(blocked_by, str) and blocked_by.strip():
        return True
    return False


def effectively_closed(task: dict[str, Any]) -> bool:
    """Detect completed tasks even when a stale status field was not normalized.

    Cowork often appends rich audit metadata (`completed_at`, `audit_verdict`,
    `delivery_artifact`) during always-on runs.  If a concurrent writer leaves
    `status` stale as READY/IN_PROGRESS, the dispatcher should still avoid
    re-feeding that task.  This keeps Cowork focused on the newest audit rather
    than burning paid time on already-delivered work.
    """
    if task.get("status") in NEVER_DISPATCH:
        return True
    if task.get("completed_at"):
        return True
    verdict = str(task.get("audit_verdict", "")).upper()
    if verdict in COMPLETION_VERDICTS:
        return True
    if task.get("delivery_artifact") or task.get("deliverable"):
        if verdict in {"DELIVERED", "AUDIT_PASS", "DONE", ""} and task.get("completed_at"):
            return True
    return False


def dispatch_unconfirmed(task: dict[str, Any]) -> bool:
    if delivery_state(task) in UNCONFIRMED_DELIVERY_STATES:
        return True
    notes = task.get("notes", [])
    if isinstance(notes, str):
        notes = [notes]
    if isinstance(notes, list):
        return any("UNCONFIRMED" in str(note).upper() for note in notes)
    return False


def stale_in_progress_diagnostic(task: dict[str, Any]) -> str | None:
    if task.get("status") != "IN_PROGRESS" or effectively_closed(task):
        return None
    age_seconds = task_age_seconds(task)
    if age_seconds < GHOST_IN_PROGRESS_DIAGNOSTIC_SECONDS:
        return None
    if diagnostic_stale_unconfirmed_in_progress(task):
        return "DIAGNOSTIC_STALE_UNCONFIRMED_IN_PROGRESS"
    if dispatch_unconfirmed(task):
        return "UNCONFIRMED_IN_PROGRESS"
    if not dispatch_confirmed(task) and age_seconds >= STALE_HOURS * 3600:
        return "STALE_WITHOUT_DELIVERY_CONFIRMATION"
    return None


def diagnostic_stale_unconfirmed_in_progress(task: dict[str, Any]) -> bool:
    """Quarantine old ghost dispatches as diagnostic-only, never as DONE.

    This path is intentionally narrower than normal stale recycling: it applies
    only to aged IN_PROGRESS tasks with no confirmed delivery and no completion
    evidence.  The task remains in the registry for auditability, but it is not
    treated as actionable fallback work after the 24h diagnostic threshold.
    """
    if task.get("status") != "IN_PROGRESS":
        return False
    if effectively_closed(task):
        return False
    if dispatch_confirmed(task) or has_completion_evidence(task):
        return False
    if task_age_seconds(task) < DIAGNOSTIC_STALE_UNCONFIRMED_HOURS * 3600:
        return False
    return dispatch_unconfirmed(task) or bool(task.get("dispatched_at"))


def unconfirmed_in_progress_requeue_candidate(task: dict[str, Any], agent: str) -> bool:
    if task.get("status") != "IN_PROGRESS":
        return False
    owner = task.get("owner", "Any")
    if owner not in {agent, "Any"}:
        return False
    if task.get("dispatched_to") not in {None, agent}:
        return False
    if dispatch_confirmed(task) or has_completion_evidence(task):
        return False
    if diagnostic_stale_unconfirmed_in_progress(task):
        return False
    if delivery_state(task) not in UNCONFIRMED_DELIVERY_STATES:
        return False
    return task_age_seconds(task) >= GHOST_IN_PROGRESS_DIAGNOSTIC_SECONDS


def in_progress_diagnostics_for(agent: str, tasks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    diagnostics: list[dict[str, Any]] = []
    for task in tasks:
        owner = task.get("owner", "Any")
        if owner not in {agent, "Any"}:
            continue
        reason = stale_in_progress_diagnostic(task)
        if reason:
            diagnostics.append(
                {
                    "task_id": task.get("id"),
                    "reason": reason,
                    "dispatched_to": task.get("dispatched_to"),
                    "delivery_state": task.get("delivery_state"),
                    "age_seconds": round(task_age_seconds(task), 1),
                }
            )
    return diagnostics


def task_text(task: dict[str, Any]) -> str:
    parts: list[str] = []
    for key in ("id", "title", "objective"):
        value = task.get(key)
        if isinstance(value, str):
            parts.append(value)
    notes = task.get("notes", [])
    if isinstance(notes, list):
        parts.extend(str(item) for item in notes)
    elif isinstance(notes, str):
        parts.append(notes)
    validation = task.get("validation", [])
    if isinstance(validation, list):
        parts.extend(str(item) for item in validation)
    elif isinstance(validation, str):
        parts.append(validation)
    return "\n".join(parts)


def parse_version_tuple(version: str) -> tuple[int, ...]:
    return tuple(int(part) for part in version.split(".") if part.isdigit())


def normalize_version_tuple(version: tuple[int, ...], width: int = 3) -> tuple[int, ...]:
    """Compare v2.64 and v2.64.0 as the same frontier version."""
    if len(version) >= width:
        return version
    return version + (0,) * (width - len(version))


def version_gt(left: tuple[int, ...], right: tuple[int, ...]) -> bool:
    width = max(len(left), len(right), 3)
    return normalize_version_tuple(left, width) > normalize_version_tuple(right, width)


def version_gte(left: tuple[int, ...], right: tuple[int, ...]) -> bool:
    width = max(len(left), len(right), 3)
    return normalize_version_tuple(left, width) >= normalize_version_tuple(right, width)


def axiom_frontier_has_version_at_least(threshold: str) -> bool:
    if not (REPO_ROOT / "AXIOM_FRONTIER.md").exists():
        return False
    text = (REPO_ROOT / "AXIOM_FRONTIER.md").read_text(
        encoding="utf-8", errors="ignore"
    )
    wanted = parse_version_tuple(threshold)
    for match in re.finditer(r"^#\s+v(\d+(?:\.\d+)*)", text, re.MULTILINE):
        if version_gte(parse_version_tuple(match.group(1)), wanted):
            return True
    return False


def axiom_frontier_latest_version() -> tuple[int, ...] | None:
    if not (REPO_ROOT / "AXIOM_FRONTIER.md").exists():
        return None
    text = (REPO_ROOT / "AXIOM_FRONTIER.md").read_text(
        encoding="utf-8", errors="ignore"
    )
    versions = [
        parse_version_tuple(match.group(1))
        for match in re.finditer(r"^#\s+v(\d+(?:\.\d+)*)", text, re.MULTILINE)
    ]
    return max(versions) if versions else None


def versioned_cowork_audit_version(task: dict[str, Any]) -> tuple[int, ...] | None:
    match = VERSIONED_COWORK_AUDIT.match(str(task.get("id", "")))
    if not match:
        return None
    return parse_version_tuple(match.group(1))


def superseded_by_newer_cowork_audit(
    task: dict[str, Any], tasks: list[dict[str, Any]]
) -> bool:
    """Avoid feeding Cowork stale v2.x audits after a newer v2 audit exists.

    The repo accumulates audit tasks for each Codex F3 milestone.  During an
    always-on GUI run, old READY audit tasks can survive long enough to consume
    Cowork cycles after a newer milestone already exists.  Cowork should audit
    the newest open version first; older entries remain in the registry for
    history but are no longer auto-dispatch candidates.
    """
    current = versioned_cowork_audit_version(task)
    if current is None:
        return False
    latest_frontier = axiom_frontier_latest_version()
    if latest_frontier is not None and version_gt(latest_frontier, current):
        return True
    for other in tasks:
        if other is task:
            continue
        if other.get("owner") != "Cowork":
            continue
        if effectively_closed(other):
            continue
        other_version = versioned_cowork_audit_version(other)
        if other_version is not None and version_gt(other_version, current):
            return True
    return False


def file_has_regex(path_text: str, pattern: str) -> bool:
    path = Path(path_text)
    if not path.is_absolute():
        path = REPO_ROOT / path
    if not path.exists() or not path.is_file():
        return False
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return False
    return re.search(pattern, text, re.MULTILINE) is not None


def history_has_task_status(task_id: str, statuses: set[str]) -> bool:
    if not HISTORY_FILE.exists():
        return False
    try:
        lines = HISTORY_FILE.read_text(encoding="utf-8", errors="ignore").splitlines()
    except OSError:
        return False
    for line in reversed(lines[-500:]):
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get("task_id") != task_id:
            continue
        status_text = " ".join(
            str(event.get(key, "")) for key in ("event", "status", "verdict", "summary")
        )
        if any(status in status_text for status in statuses):
            return True
    return False


def task_status(tasks: list[dict[str, Any]], task_id: str) -> str | None:
    for item in tasks:
        if item.get("id") == task_id:
            status = item.get("status")
            return str(status) if status is not None else None
    return None


def task_by_id(tasks: list[dict[str, Any]], task_id: str) -> dict[str, Any] | None:
    for item in tasks:
        if item.get("id") == task_id:
            return item
    return None


def _extend_text_from_value(parts: list[str], value: Any) -> None:
    if isinstance(value, str):
        parts.append(value)
    elif isinstance(value, list):
        parts.extend(str(item) for item in value)


def codex_substrate_ids_for_cowork_audit(task: dict[str, Any]) -> list[str]:
    """Return concrete Codex task ids named by a Cowork audit slot.

    This is a rate-limit guard for audit slots, not a polling-spam gate.  It only
    applies to Cowork audit tasks that explicitly name a Codex substrate task.
    Version labels embedded in audit-family ids such as
    `COWORK-AUDIT-CODEX-V2.169-...` are ignored because they are audit names,
    not Codex substrate task ids.
    """
    if task.get("owner") != "Cowork":
        return []
    task_id = str(task.get("id", ""))
    if not task_id.startswith("COWORK-AUDIT-CODEX-"):
        return []

    parts: list[str] = []
    for key in (
        "id",
        "title",
        "objective",
        "source_task",
        "source_recommendation",
        "audit_summary",
        "deferral_reason",
        "abandonment_reason",
    ):
        _extend_text_from_value(parts, task.get(key))
    for key in ("notes", "validation", "stop_if"):
        _extend_text_from_value(parts, task.get(key))

    ids = {
        match.group(0)
        for text in parts
        for match in CODEX_TASK_ID_RE.finditer(text)
        if not re.match(r"^CODEX-V\d", match.group(0))
    }
    return sorted(ids)


def substrate_task_completed(
    task_id: str,
    tasks: list[dict[str, Any]],
    seen: set[str] | None = None,
) -> bool:
    seen = set() if seen is None else seen
    if task_id in seen:
        return False
    seen.add(task_id)
    task = task_by_id(tasks, task_id)
    if task is not None:
        if effectively_closed(task) or str(task.get("status", "")).upper() == "DONE":
            return True
        for key in ("superseded_by", "resolved_by", "completed_by"):
            successor = task.get(key)
            if isinstance(successor, str) and successor and successor != task_id:
                if substrate_task_completed(successor, tasks, seen):
                    return True
    return history_has_task_status(
        task_id,
        {"task_completed", "DONE", "RESOLVED", "AUDIT_PASS"},
    )


def cowork_audit_waiting_on_unlanded_substrate(
    task: dict[str, Any],
    tasks: list[dict[str, Any]],
) -> tuple[bool, str]:
    """Defer repeated Cowork audit slots until their Codex substrate lands.

    Cowork should stay busy, but not by repeatedly auditing the same absent
    substrate.  If at least one named substrate is already complete, the audit is
    allowed.  If no named substrate is known to the registry/history, the audit is
    also allowed so Cowork can diagnose the mismatch rather than being hidden.
    """
    substrate_ids = codex_substrate_ids_for_cowork_audit(task)
    if not substrate_ids:
        return False, ""

    known_substrates = [
        task_id for task_id in substrate_ids
        if task_by_id(tasks, task_id) is not None
        or history_has_task_status(
            task_id,
            {"dispatch_task", "task_completed", "DONE", "RESOLVED", "AUDIT_PASS"},
        )
    ]
    if not known_substrates:
        return False, ""
    if any(substrate_task_completed(task_id, tasks) for task_id in known_substrates):
        return False, ""

    dispatched_at = parse_time(task.get("dispatched_at"))
    if dispatched_at != datetime.min.replace(tzinfo=timezone.utc):
        age = (datetime.now(timezone.utc) - dispatched_at).total_seconds()
        if age < COWORK_AUDIT_SUBSTRATE_WAIT_SECONDS:
            return True, (
                "AUDIT_SUBSTRATE_PENDING_RECENT:"
                + ",".join(known_substrates)
            )
    return True, "AUDIT_SUBSTRATE_PENDING:" + ",".join(known_substrates)


def is_cowork_polling_task_id(task_id: str) -> bool:
    # META tasks create new actionable work; they must never be throttled as
    # Cowork polling audits.
    if task_id in META_TASK_IDS or task_id.startswith("META-"):
        return False
    return any(task_id.startswith(prefix) for prefix in COWORK_POLLING_TASK_PREFIXES)


def future_trigger_state(
    task: dict[str, Any],
    tasks: list[dict[str, Any]],
    log_miss: bool = True,
) -> tuple[bool, str]:
    """Evaluate explicit FUTURE auto-promote triggers without overclaiming.

    Unknown trigger language is treated as not fired and logged, so a trigger-gated
    FUTURE task cannot repeatedly route around Cowork's audit discipline.
    """
    text = task_text(task)
    lower = text.lower()
    trigger_state = str(task.get("trigger_state", "")).strip().upper()
    trigger_name = str(task.get("trigger", "")).strip()
    if trigger_state:
        fired_states = {"FIRED", "TRIGGER_FIRED", "READY", "ACTIVATED"}
        if trigger_state in fired_states:
            return True, f"TRIGGER_STATE:{trigger_state}"
        if log_miss:
            append_history(
                {
                    "time": utc_now(),
                    "event": "trigger_not_fired",
                    "agent": "dispatcher",
                    "task_id": task.get("id"),
                    "reason": f"TRIGGER_STATE_{trigger_state}",
                }
            )
        return False, f"TRIGGER_STATE:{trigger_state}"

    if trigger_name:
        if log_miss:
            append_history(
                {
                    "time": utc_now(),
                    "event": "trigger_not_fired",
                    "agent": "dispatcher",
                    "task_id": task.get("id"),
                    "reason": f"TRIGGER_FIELD_NOT_FIRED:{trigger_name}",
                }
            )
        return False, f"TRIGGER_FIELD_NOT_FIRED:{trigger_name}"

    has_explicit_future_gate = any(
        phrase in lower
        for phrase in (
            "auto-promote",
            "auto-promotes",
            "auto_promote",
            "auto_promotes",
            "auto-activate",
            "auto-activates",
            "auto-activated",
            "auto_activate",
            "auto_activates",
            "auto_activated",
        )
    )
    if not has_explicit_future_gate:
        return True, "NO_EXPLICIT_TRIGGER"

    # Common audit-followup shape: "When DONE, TASK-X auto-promotes".
    done_ids = set(re.findall(r"\b([A-Z][A-Z0-9.-]+-[A-Z0-9.-]+-\d{3})\b", text))
    done_ids.discard(str(task.get("id", "")))
    for task_id in sorted(done_ids):
        if "when DONE" in text or "When DONE" in text or "when done" in lower:
            if task_status(tasks, task_id) == "DONE" or history_has_task_status(
                task_id, {"DONE", "complete_task", "audit_pass"}
            ):
                return True, f"TASK_DONE:{task_id}"

    # AXIOM_FRONTIER version gates, e.g. "commits a v2.52+ to AXIOM_FRONTIER.md".
    for version in re.findall(r"\bv(\d+(?:\.\d+)*)\+", text):
        if "AXIOM_FRONTIER" in text and axiom_frontier_has_version_at_least(version):
            return True, f"AXIOM_FRONTIER_VERSION_AT_LEAST:v{version}"

    # Grep-style gates in task notes/objectives.
    grep_patterns = [
        (r"grep\s+([^\n]+?)\s+(YangMills/[^\s,;]+\.lean)", "generic_grep"),
        (r"\^theorem\.\*(leaf|deletion_order|deletionOrder|nontrivialAnchored|preserves_preconnected|existsNonRoot)[^\n]*?(YangMills/[^\s,;]+\.lean)", "theorem_grep"),
    ]
    for regex, _kind in grep_patterns:
        for match in re.finditer(regex, text):
            raw_pattern = match.group(1)
            raw_file = match.group(2)
            pattern = raw_pattern.strip().strip("`'\"")
            if pattern.startswith("^theorem.*"):
                regex_pattern = pattern
            else:
                regex_pattern = re.escape(pattern)
            if file_has_regex(raw_file, regex_pattern):
                return True, f"GREP_MATCH:{raw_file}:{pattern}"

    # Known F3 audit gate after Codex v2.52: the local degree-one subcase is
    # auditable, but it is still not the global deletion-order theorem.
    if str(task.get("id")) == "COWORK-AUDIT-CLAY-F3-COUNT-LEAF-DELETION-001":
        if file_has_regex(
            "YangMills/ClayCore/LatticeAnimalCount.lean",
            r"^theorem\s+plaquetteGraphPreconnectedSubsetsAnchoredCard_erase_mem_of_induced_degree_one",
        ) and axiom_frontier_has_version_at_least("2.52.0"):
            return True, "F3_V2_52_DEGREE_ONE_LEAF_SUBCASE"

    if log_miss:
        append_history(
            {
                "time": utc_now(),
                "event": "trigger_not_fired",
                "agent": "dispatcher",
                "task_id": task.get("id"),
                "reason": "TRIGGER_NOT_FIRED_OR_NOT_PARSED",
            }
        )
    return False, "TRIGGER_NOT_FIRED_OR_NOT_PARSED"


def recently_dispatched_same_agent(task: dict[str, Any], agent: str, state: dict[str, Any]) -> bool:
    by_agent = state.get("last_dispatch_by_agent")
    if isinstance(by_agent, dict):
        agent_state = by_agent.get(agent)
        if isinstance(agent_state, dict) and task.get("id") == agent_state.get("task_id"):
            dispatched_at = parse_time(agent_state.get("at"))
            if dispatched_at != datetime.min.replace(tzinfo=timezone.utc):
                age = datetime.now(timezone.utc) - dispatched_at
                if age.total_seconds() < RECENT_REPEAT_SUPPRESS_SECONDS:
                    return True
    if task.get("id") != state.get("last_dispatched_task"):
        return False
    if agent != state.get("last_dispatched_agent"):
        return False
    dispatched_at = parse_time(state.get("last_dispatch_at"))
    if dispatched_at == datetime.min.replace(tzinfo=timezone.utc):
        return False
    age = datetime.now(timezone.utc) - dispatched_at
    return age.total_seconds() < RECENT_REPEAT_SUPPRESS_SECONDS


def task_rank(task: dict[str, Any], state: dict[str, Any]) -> tuple[int, int, int, str, str]:
    status = task.get("status", "READY")
    if status in PRIMARY_STATUSES:
        status_rank = PRIMARY_STATUSES[status]
    elif status == "IN_PROGRESS" and is_stale(task):
        status_rank = FALLBACK_STATUSES[status]
    elif status == "FUTURE":
        status_rank = FALLBACK_STATUSES[status]
    else:
        status_rank = 50
    repeat_penalty = 1 if task.get("id") == state.get("last_dispatched_task") else 0
    return (
        status_rank,
        int(task.get("priority", 999)),
        repeat_penalty,
        str(task.get("created_at", "")),
        str(task.get("id", "")),
    )


def task_is_actionable_for(
    agent: str,
    task: dict[str, Any],
    allow_future: bool,
    state: dict[str, Any],
    tasks: list[dict[str, Any]],
    log_trigger_misses: bool = True,
) -> bool:
    owner = task.get("owner", "Any")
    status = task.get("status", "READY")
    if owner not in {agent, "Any"}:
        return False
    if effectively_closed(task):
        return False
    if is_blocked(task):
        return False
    if agent == "Cowork" and superseded_by_newer_cowork_audit(task, tasks):
        return False
    if agent == "Cowork":
        waiting_on_substrate, _reason = cowork_audit_waiting_on_unlanded_substrate(task, tasks)
        if waiting_on_substrate:
            return False
    if recently_dispatched_same_agent(task, agent, state):
        return False
    if status in PRIMARY_STATUSES:
        return True
    if status == "IN_PROGRESS":
        return is_stale(task) or unconfirmed_in_progress_requeue_candidate(task, agent)
    if status == "FUTURE":
        if not allow_future:
            return False
        fired, _reason = future_trigger_state(
            task, tasks, log_miss=log_trigger_misses
        )
        if (
            agent == "Cowork"
            and _reason == "NO_EXPLICIT_TRIGGER"
            and is_cowork_polling_task_id(str(task.get("id", "")))
        ):
            return False
        return fired
    return False


def select_next_task(
    agent: str,
    tasks: list[dict[str, Any]],
    state: dict[str, Any],
    log_trigger_misses: bool = True,
) -> dict[str, Any] | None:
    primary = [
        task for task in tasks
        if task_is_actionable_for(
            agent, task, allow_future=False, state=state, tasks=tasks,
            log_trigger_misses=log_trigger_misses,
        )
    ]
    if primary:
        return sorted(primary, key=lambda task: task_rank(task, state))[0]
    fallback = [
        task for task in tasks
        if task_is_actionable_for(
            agent, task, allow_future=True, state=state, tasks=tasks,
            log_trigger_misses=log_trigger_misses,
        )
    ]
    if fallback:
        return sorted(fallback, key=lambda task: task_rank(task, state))[0]
    return None


def list_block(title: str, values: Any) -> str:
    if not values:
        return f"{title}:\n- none"
    if isinstance(values, str):
        values = [values]
    return title + ":\n" + "\n".join(f"- {sanitize_output_text(str(item))}" for item in values)


def sanitize_output_text(text: str) -> str:
    """Prevent generated dispatch messages from echoing forbidden prompts."""
    replacements = {
        "muy bien, continúa": "[forbidden generic phrase redacted]",
        "muy bien, continÃºa": "[forbidden generic phrase redacted]",
        "muy bien, contin�a": "[forbidden generic phrase redacted]",
        'MESSAGE = "muy bien, continúa!"': "the old fixed generic MESSAGE assignment",
        'MESSAGE = "muy bien, continÃºa!"': "the old fixed generic MESSAGE assignment",
        'MESSAGE = "muy bien, contin�a!"': "the old fixed generic MESSAGE assignment",
    }
    cleaned = text
    for old, new in replacements.items():
        cleaned = cleaned.replace(old, new)
    return cleaned


def build_task_message(agent: str, task: dict[str, Any]) -> str:
    required_updates = [
        "AGENT_BUS.md",
        "registry/agent_tasks.yaml",
        "registry/agent_history.jsonl",
        "dashboard/agent_state.json",
    ]
    if agent == "Cowork":
        required_updates.extend(["COWORK_RECOMMENDATIONS.md", "registry/recommendations.yaml"])
    return "\n".join(
        [
            "## Structured Agent Dispatch",
            "",
            f"Agent role: {agent}",
            f"Task id: {task.get('id')}",
            f"Task title: {task.get('title')}",
            f"Task priority: {task.get('priority')}",
            f"Task status at dispatch: {task.get('status')}",
            "",
            list_block("Files to read", task.get("required_files")),
            "",
            "Objective:",
            sanitize_output_text(str(task.get("objective", "")).strip()),
            "",
            list_block("Validation requirements", task.get("validation")),
            "",
            list_block("Stop conditions", task.get("stop_if")),
            "",
            list_block("Required updates", required_updates),
            "",
            "Next exact instruction:",
            (
                f"> {agent}, take task `{task.get('id')}`. Read the files above, "
                "perform the objective, run or satisfy the validation requirements, "
                "update the required registries, and stop if any listed stop condition is met."
            ),
        ]
    )


def build_meta_message(agent: str) -> str:
    files = [
        "FORMALIZATION_ROADMAP_CLAY.md",
        "UNCONDITIONALITY_LEDGER.md",
        "registry/recommendations.yaml",
        "AGENT_BUS.md",
        "registry/agent_tasks.yaml",
    ]
    return "\n".join(
        [
            "## Structured Agent Dispatch",
            "",
            f"Agent role: {agent}",
            "Task id: META-GENERATE-TASKS-001",
            "Task title: Generate new actionable tasks when the queue is empty",
            "Task priority: 99",
            "Task status at dispatch: META",
            "",
            list_block("Files to read", files),
            "",
            "Objective:",
            (
                "No actionable READY or PARTIAL task exists for this agent. Inspect "
                "the roadmap, ledger, recommendations, and bus, then create at least "
                "three new READY tasks that reduce conditionality, improve auditability, "
                "or repair the agentic infrastructure."
            ),
            "",
            list_block(
                "Validation requirements",
                ["registry/agent_tasks.yaml contains at least three READY tasks"],
            ),
            "",
            list_block(
                "Stop conditions",
                ["Roadmap and ledger are missing", "Cannot write registry/agent_tasks.yaml"],
            ),
            "",
            list_block(
                "Required updates",
                [
                    "registry/agent_tasks.yaml",
                    "registry/agent_history.jsonl",
                    "dashboard/agent_state.json",
                    "AGENT_BUS.md",
                ],
            ),
            "",
            "Next exact instruction:",
            (
                f"> {agent}, create at least three READY tasks from the roadmap, "
                "ledger, recommendations, and bus; validate that the queue is actionable; "
                "then hand off to the appropriate next agent."
            ),
        ]
    )


def record_yaml_registry_error(agent: str, error: YAMLRegistryError) -> None:
    now = utc_now()
    payload = {
        "timestamp": now,
        "agent": agent,
        "event": "yaml_registry_parse_error",
        "path": str(error.path),
        "error": str(error.original),
    }
    (REPO_ROOT / "dashboard").mkdir(parents=True, exist_ok=True)
    save_json(REPO_ROOT / "dashboard" / "last_yaml_error.json", payload)
    append_history(payload)


def build_yaml_repair_message(agent: str, error: YAMLRegistryError) -> str:
    err_text = sanitize_output_text(str(error.original)).strip()
    files = [
        str(error.path),
        "dashboard/last_yaml_error.json",
        "registry/agent_history.jsonl",
        "AGENT_BUS.md",
    ]
    return "\n".join(
        [
            "## Structured Agent Dispatch",
            "",
            f"Agent role: {agent}",
            "Task id: META-YAML-REPAIR-001",
            "Task title: Repair malformed shared YAML registry",
            "Task priority: 0",
            "Task status at dispatch: EMERGENCY",
            "",
            list_block("Files to read", files),
            "",
            "Objective:",
            (
                f"The dispatcher could not parse `{error.path}`. Repair only the "
                "malformed YAML syntax, preserve all existing task content, then "
                "validate that the canonical dispatcher can emit structured tasks "
                "for both Codex and Cowork."
            ),
            "",
            "Parser error:",
            err_text,
            "",
            list_block(
                "Validation requirements",
                [
                    f"python -c \"import yaml, pathlib; yaml.safe_load(pathlib.Path(r'{error.path}').read_text(encoding='utf-8')); print('yaml ok')\"",
                    "python scripts\\agent_next_instruction.py Codex --peek",
                    "python scripts\\agent_next_instruction.py Cowork --peek",
                    "python C:\\Users\\lluis\\Downloads\\codex_autocontinue.py --codex-only",
                ],
            ),
            "",
            list_block(
                "Stop conditions",
                [
                    "Do not delete existing tasks to make YAML parse",
                    "Do not mark any mathematical task DONE during syntax repair",
                    "Stop if the file has conflicting duplicate task ids that need human review",
                ],
            ),
            "",
            list_block(
                "Required updates",
                [
                    "registry/agent_tasks.yaml or the malformed YAML file named above",
                    "registry/agent_history.jsonl",
                    "dashboard/last_yaml_error.json",
                    "AGENT_BUS.md",
                ],
            ),
            "",
            "Next exact instruction:",
            (
                f"> {agent}, take task `META-YAML-REPAIR-001`. Repair the malformed "
                "YAML registry named above without deleting tasks, run the validation "
                "commands, update the history and bus, and stop if duplicate task ids "
                "or ambiguous conflicting edits require human review."
            ),
        ]
    )


def mark_task_dispatched(tasks_doc: dict[str, Any], task_id: str, agent: str) -> None:
    now = utc_now()
    for task in tasks_doc.get("tasks", []):
        if task.get("id") == task_id:
            requeue_unconfirmed = unconfirmed_in_progress_requeue_candidate(task, agent)
            if task.get("status") in {"READY", "PARTIAL", "FUTURE"}:
                task["status"] = "IN_PROGRESS"
            if requeue_unconfirmed:
                task["quarantined_unconfirmed_at"] = now
                task["quarantine_requeue_count"] = int(task.get("quarantine_requeue_count", 0)) + 1
            task["updated_at"] = now
            task["dispatched_at"] = now
            task["dispatched_to"] = agent
            task["delivery_state"] = "DISPATCH_MUTATED_PENDING_CONFIRMATION"
            task["delivery_attempted_at"] = now
            task.pop("delivery_confirmed_at", None)
            task.pop("delivery_unconfirmed_at", None)
            task["dispatch_count"] = int(task.get("dispatch_count", 0)) + 1
            notes = task.setdefault("notes", [])
            notes.append(
                f"Dispatched to {agent} at {now}; awaiting visual busy confirmation"
            )
            if requeue_unconfirmed:
                notes.append(
                    "Re-dispatched after conservative unconfirmed-IN_PROGRESS "
                    "quarantine checks: aged pending delivery, same agent, "
                    "no completion evidence, and no confirmed busy delivery."
                )
            return


def record_delivery_state(
    agent: str,
    task_id: str,
    state_name: str,
    method: str = "",
    distance: str = "",
) -> None:
    now = utc_now()
    normalized_state = state_name.upper()
    with coordination_lock():
        tasks_doc = load_yaml(TASKS_FILE)
        found = False
        for task in tasks_doc.get("tasks", []):
            if task.get("id") != task_id:
                continue
            found = True
            task["delivery_state"] = normalized_state
            task["delivery_updated_at"] = now
            task["delivery_agent"] = agent
            if method:
                task["last_delivery_method"] = method
            if distance:
                task["last_delivery_distance"] = distance
            if normalized_state in CONFIRMED_DELIVERY_STATES:
                task["delivery_confirmed_at"] = now
                task.pop("delivery_unconfirmed_at", None)
            elif normalized_state in UNCONFIRMED_DELIVERY_STATES:
                task["delivery_unconfirmed_at"] = now
                if (
                    normalized_state == "ABANDONED_UNCONFIRMED"
                    and not dispatch_confirmed(task)
                    and not has_completion_evidence(task)
                ):
                    task["status"] = "READY"
                    task["requeued_after_abandoned_unconfirmed_at"] = now
            notes = task.setdefault("notes", [])
            notes.append(
                f"Delivery state for {agent} recorded as {normalized_state} at {now}"
            )
            break
        if not found:
            raise SystemExit(f"Task id not found for delivery state update: {task_id}")
        save_yaml(TASKS_FILE, tasks_doc)
        append_history(
            {
                "time": now,
                "event": "dispatch_delivery_state",
                "agent": agent,
                "task_id": task_id,
                "delivery_state": normalized_state,
                "method": method,
                "distance": distance,
            }
        )


def update_dashboard(agent: str, task_id: str | None, meta: bool = False) -> None:
    state = INITIAL_STATE | load_json(STATE_FILE)
    now = utc_now()
    state["current_baton_owner"] = agent
    state["last_dispatched_agent"] = agent
    state["last_dispatched_task"] = task_id
    state["last_dispatch_at"] = now
    by_agent = state.get("last_dispatch_by_agent")
    if not isinstance(by_agent, dict):
        by_agent = {}
    by_agent[agent] = {"task_id": task_id, "at": now}
    state["last_dispatch_by_agent"] = by_agent
    state["next_task_id"] = task_id
    state["always_has_next_task"] = True
    if meta:
        state["current_phase"] = "task_generation_needed"
    save_json(STATE_FILE, state)


def _build_message_unlocked(
    agent: str,
    mutate: bool = True,
    skip_cowork_polling: bool = False,
) -> str:
    if agent not in VALID_AGENTS:
        raise SystemExit(f"Unknown agent role '{agent}'. Use Codex or Cowork.")
    if mutate:
        ensure_base_files()
    tasks_doc = load_yaml(TASKS_FILE)
    state = load_json(STATE_FILE)
    candidate_tasks = tasks_doc.get("tasks", [])
    if agent == "Cowork" and skip_cowork_polling:
        candidate_tasks = [
            task for task in candidate_tasks
            if not is_cowork_polling_task_id(str(task.get("id", "")))
        ]
    task = select_next_task(
        agent,
        candidate_tasks,
        state,
        log_trigger_misses=mutate,
    )
    diagnostics = in_progress_diagnostics_for(agent, tasks_doc.get("tasks", []))
    diagnostic_stale = [
        item for item in diagnostics
        if item.get("reason") == "DIAGNOSTIC_STALE_UNCONFIRMED_IN_PROGRESS"
    ]
    if mutate and diagnostic_stale:
        previous_ids = {
            str(item.get("task_id"))
            for item in state.get("diagnostic_stale_in_progress", [])
            if isinstance(item, dict)
        }
        current_ids = {str(item.get("task_id")) for item in diagnostic_stale}
        state["last_in_progress_dispatch_diagnostic"] = {
            "agent": agent,
            "at": utc_now(),
            "candidates": diagnostics[:5],
        }
        state["diagnostic_stale_in_progress"] = diagnostic_stale[:20]
        save_json(STATE_FILE, state)
        if current_ids != previous_ids:
            append_history(
                {
                    "time": utc_now(),
                    "event": "diagnostic_stale_in_progress",
                    "agent": agent,
                    "candidates": diagnostic_stale[:20],
                }
            )
    if task is None:
        message = build_meta_message(agent)
        if mutate:
            if diagnostics:
                state["last_in_progress_dispatch_diagnostic"] = {
                    "agent": agent,
                    "at": utc_now(),
                    "candidates": diagnostics[:5],
                }
                save_json(STATE_FILE, state)
                append_history(
                    {
                        "time": utc_now(),
                        "event": "in_progress_dispatch_diagnostic",
                        "agent": agent,
                        "candidates": diagnostics[:5],
                    }
                )
            update_dashboard(agent, "META-GENERATE-TASKS-001", meta=True)
            append_history(
                {
                    "time": utc_now(),
                    "event": "dispatch_meta_task",
                    "agent": agent,
                    "task_id": "META-GENERATE-TASKS-001",
                }
            )
        return message

    message_task = deepcopy(task)
    if mutate:
        mark_task_dispatched(tasks_doc, task["id"], agent)
        save_yaml(TASKS_FILE, tasks_doc)
        update_dashboard(agent, task["id"])
        append_history(
            {
                "time": utc_now(),
                "event": "dispatch_task",
                "agent": agent,
                "task_id": task["id"],
                "task_title": task.get("title"),
                "priority": task.get("priority"),
            }
        )
    return build_task_message(agent, message_task)


def build_message(
    agent: str,
    mutate: bool = True,
    skip_cowork_polling: bool = False,
) -> str:
    with coordination_lock():
        return _build_message_unlocked(
            agent,
            mutate=mutate,
            skip_cowork_polling=skip_cowork_polling,
        )


def _pop_cli_option(argv: list[str], name: str, default: str = "") -> str:
    if name not in argv:
        return default
    idx = argv.index(name)
    argv.pop(idx)
    if idx >= len(argv):
        return default
    return argv.pop(idx)


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if "--record-delivery" in argv:
        argv.remove("--record-delivery")
        agent = _pop_cli_option(argv, "--agent", "Codex")
        task_id = _pop_cli_option(argv, "--task-id")
        state_name = _pop_cli_option(argv, "--state")
        method = _pop_cli_option(argv, "--method")
        distance = _pop_cli_option(argv, "--distance")
        if not task_id or not state_name:
            raise SystemExit("--record-delivery requires --task-id and --state")
        record_delivery_state(agent, task_id, state_name, method, distance)
        return 0

    mutate = True
    if "--peek" in argv:
        mutate = False
        argv.remove("--peek")
    skip_cowork_polling = False
    if "--skip-cowork-polling" in argv:
        skip_cowork_polling = True
        argv.remove("--skip-cowork-polling")
    agent = argv[0] if argv else "Codex"
    try:
        print(build_message(
            agent,
            mutate=mutate,
            skip_cowork_polling=skip_cowork_polling,
        ))
    except YAMLRegistryError as exc:
        with coordination_lock():
            record_yaml_registry_error(agent, exc)
        print(build_yaml_repair_message(agent, exc))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
