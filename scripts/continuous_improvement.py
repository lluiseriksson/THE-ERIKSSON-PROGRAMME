#!/usr/bin/env python3
"""Continuous-improvement diagnostic for the Codex/Cowork research loop.

This script is intentionally conservative: it does not claim mathematical
progress and it does not mutate task statuses. It gives the watcher a compact
daily health check over queue coverage, role balance, stale dispatch risk, and
missing work lanes toward the Clay-level goal.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import yaml


REPO_ROOT = Path(r"C:\Users\lluis\.gemini\antigravity\scratch\THE-ERIKSSON-PROGRAMME")
TASKS_FILE = REPO_ROOT / "registry" / "agent_tasks.yaml"
STATE_FILE = REPO_ROOT / "dashboard" / "agent_state.json"
HISTORY_FILE = REPO_ROOT / "registry" / "agent_history.jsonl"
REPORT_FILE = REPO_ROOT / "dashboard" / "continuous_improvement_status.json"
PLAYBOOK_FILE = REPO_ROOT / "dashboard" / "continuous_improvement_playbook.md"

ACTIVE_STATUSES = {"READY", "PARTIAL", "IN_PROGRESS"}
QUEUE_STATUSES = {"READY", "PARTIAL"}
TERMINAL_STATUSES = {"DONE", "CANCELLED", "BLOCKED", "SUPERSEDED"}
CODEX_READY_FLOOR = 3

LANES = {
    "formal_math": {
        "description": "Lean/formal theorem work that reduces a named mathematical blocker.",
        "keywords": ("F3-", "PROVE", "INTERFACE", "SCOPE", "LEAN", "THEOREM"),
        "min_ready": 1,
    },
    "creative_research": {
        "description": "Cowork/strategy work inventing non-circular mathematical routes.",
        "keywords": ("CREATIVE", "BRAINSTORM", "RESEARCH", "PAPER", "STRATEGY"),
        "min_ready": 1,
    },
    "audit_honesty": {
        "description": "Ledger, horizon, progress, and claim-safety auditing.",
        "keywords": ("AUDIT", "LEDGER", "HORIZON", "CONSISTENCY", "FRESHNESS"),
        "min_ready": 1,
    },
    "automation_infra": {
        "description": "Watcher, dispatcher, registry, and queue reliability work.",
        "keywords": ("AUTOCONTINUE", "DISPATCHER", "REGISTRY", "QUEUE", "GHOST"),
        "min_ready": 1,
    },
    "planning_metrics": {
        "description": "Roadmap, metrics, milestones, dependencies, and time planning.",
        "keywords": ("ROADMAP", "PLANNER", "METRICS", "DEPENDENCY", "MILESTONE"),
        "min_ready": 1,
    },
}

ROLE_ROTATION = [
    {
        "role": "Codex-Implementer",
        "agent": "Codex",
        "purpose": "Land Lean interfaces/proofs or infrastructure patches with validation.",
    },
    {
        "role": "Cowork-CreativeResearch",
        "agent": "Cowork",
        "purpose": "Invent candidate invariants, theorem statements, and non-circular proof routes.",
    },
    {
        "role": "Cowork-Auditor",
        "agent": "Cowork",
        "purpose": "Attack claims, check ledgers, and block fake percentage/status movement.",
    },
    {
        "role": "Codex-Infrastructure",
        "agent": "Codex",
        "purpose": "Improve watcher, dispatcher, validation, and registry automation.",
    },
    {
        "role": "Planner",
        "agent": "Codex/Cowork",
        "purpose": "Turn blockers into dated, lane-balanced tasks.",
    },
]

SEED_TASK_TEMPLATES = [
    {
        "id": "CODEX-F3-ADMISSIBLE-VALUE-SEPARATION-CANDIDATE-LEMMA-INVENTORY-001",
        "lane": "formal_math",
        "reason": "Inventory existing Lean residual/bookkeeping helpers for the v2.207 admissible-value separation proof route.",
    },
    {
        "id": "CODEX-F3-BOOKKEEPING-TAG-ADMISSIBLE-VALUE-SEPARATION-BLOCKER-SCOPE-001",
        "lane": "formal_math",
        "reason": "Scope the next no-closure blocker if the v2.207 admissible-value separation theorem cannot be proved directly.",
    },
    {
        "id": "CODEX-AXIOM-FRONTIER-F3-V2.203-V2.207-RECONCILE-SCOPE-001",
        "lane": "audit_honesty",
        "reason": "Scope AXIOM_FRONTIER reconciliation for the bookkeeping-tag coordinate/admissible-value chain without moving status.",
    },
    {
        "id": "CODEX-LEDGER-F3-COUNT-EVIDENCE-COLUMN-EXTEND-V2.183-V2.207-SCOPE-001",
        "lane": "audit_honesty",
        "reason": "Scope the next F3-COUNT evidence-column extension through the v2.207 interface landing if artifacts support it.",
    },
    {
        "id": "CODEX-CONTINUOUS-IMPROVEMENT-TEMPLATE-EXHAUSTION-AUDIT-001",
        "lane": "automation_infra",
        "reason": "Audit whether deterministic seed templates are becoming exhausted after long unattended runs.",
    },
    {
        "id": "CODEX-F3-SELECTOR-ADMISSIBLE-BOOKKEEPING-TAG-ROUTE-PLAN-001",
        "lane": "planning_metrics",
        "reason": "Turn the selector-admissible bookkeeping-tag separation blocker into a dated theorem-dependency plan.",
    },
    {
        "id": "CODEX-F3-PROVE-ABSOLUTE-SELECTED-VALUE-CODE-AFTER-INTERFACE-001",
        "lane": "formal_math",
        "reason": "Use the v2.170 Lean interface landing to attempt or precisely fail the next theorem.",
    },
    {
        "id": "CODEX-LEDGER-F3-COUNT-EVIDENCE-COLUMN-EXTEND-V2.170-001",
        "lane": "audit_honesty",
        "reason": "Keep F3-COUNT evidence navigation current without changing conditionality.",
    },
    {
        "id": "CODEX-AXIOM-FRONTIER-F3-V2.169-V2.170-RECONCILE-001",
        "lane": "audit_honesty",
        "reason": "Reconcile AXIOM_FRONTIER with the v2.169 stop and v2.170 interface landing.",
    },
    {
        "id": "CODEX-CONTINUOUS-IMPROVEMENT-READY-FLOOR-VALIDATION-001",
        "lane": "automation_infra",
        "reason": "Audit the overnight READY floor and refine concrete task seeding if needed.",
    },
    {
        "id": "CODEX-CONTINUOUS-IMPROVEMENT-SEED-TEMPLATE-REFRESH-001",
        "lane": "automation_infra",
        "reason": "Refresh exhausted deterministic seed templates so preflight warnings name concrete follow-up work.",
    },
    {
        "id": "CODEX-AXIOM-FRONTIER-F3-V2.183-V2.187-RECONCILE-SCOPE-001",
        "lane": "audit_honesty",
        "reason": "Scope AXIOM_FRONTIER reconciliation for the v2.183-v2.187 selector-source/data-source chain without moving status.",
    },
    {
        "id": "CODEX-F3-NONSINGLETON-WALK-SPLIT-CANDIDATE-LEMMA-INVENTORY-001",
        "lane": "formal_math",
        "reason": "Inventory existing Lean graph/residual helpers for the non-singleton member neighbor walk-split blocker.",
    },
    {
        "id": "CODEX-LEDGER-F3-COUNT-EVIDENCE-COLUMN-EXTEND-V2.183-V2.187-SCOPE-001",
        "lane": "audit_honesty",
        "reason": "Scope the next F3-COUNT evidence-column extension only if dashboard artifacts support it.",
    },
]


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_yaml(path: Path) -> Any:
    if not path.exists() or not path.read_text(encoding="utf-8").strip():
        return {}
    return yaml.safe_load(path.read_text(encoding="utf-8"))


def load_json(path: Path) -> Any:
    if not path.exists() or not path.read_text(encoding="utf-8").strip():
        return {}
    return json.loads(path.read_text(encoding="utf-8-sig"))


def task_blob(task: dict[str, Any]) -> str:
    values: list[str] = []
    for key in ("id", "title", "objective"):
        if isinstance(task.get(key), str):
            values.append(task[key])
    for key in ("notes", "validation", "stop_if"):
        value = task.get(key)
        if isinstance(value, list):
            values.extend(str(item) for item in value)
        elif isinstance(value, str):
            values.append(value)
    return "\n".join(values).upper()


def classify_lanes(task: dict[str, Any]) -> list[str]:
    blob = task_blob(task)
    lanes = []
    for lane, meta in LANES.items():
        if any(keyword in blob for keyword in meta["keywords"]):
            lanes.append(lane)
    return lanes or ["unclassified"]


def parse_time(value: Any) -> datetime | None:
    if not isinstance(value, str):
        return None
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None


def seconds_since(value: Any) -> float | None:
    parsed = parse_time(value)
    if parsed is None:
        return None
    return (datetime.now(timezone.utc) - parsed).total_seconds()


def recent_history_counts(limit: int = 250) -> Counter:
    counts: Counter = Counter()
    if not HISTORY_FILE.exists():
        return counts
    lines = HISTORY_FILE.read_text(encoding="utf-8", errors="replace").splitlines()[-limit:]
    for line in lines:
        if not line.strip():
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            counts["history_parse_errors"] += 1
            continue
        counts[str(event.get("event", "<missing>"))] += 1
    return counts


def existing_task_ids(tasks: list[Any]) -> set[str]:
    return {str(task.get("id", "")) for task in tasks if isinstance(task, dict)}


def recommended_seed_tasks(tasks: list[Any], ready_by_agent: dict[str, list[str]]) -> list[dict[str, str]]:
    """Suggest deterministic concrete Codex tasks without mutating the registry.

    The watcher may call this diagnostic in preflight. Keeping it read-only avoids
    duplicate task creation or surprise status churn, while still exposing a
    ready-floor plan that META/dispatcher tasks can enact deliberately.
    """
    current_ready = len(ready_by_agent.get("Codex", []))
    needed = max(0, CODEX_READY_FLOOR - current_ready)
    if needed == 0:
        return []
    known_ids = existing_task_ids(tasks)
    suggestions = []
    for template in SEED_TASK_TEMPLATES:
        if template["id"] not in known_ids:
            suggestions.append(template)
        if len(suggestions) >= needed:
            break
    return suggestions


def build_report() -> dict[str, Any]:
    tasks_doc = load_yaml(TASKS_FILE)
    tasks = tasks_doc.get("tasks", []) if isinstance(tasks_doc, dict) else []
    state = load_json(STATE_FILE)

    counts_by_status = Counter(str(task.get("status", "UNKNOWN")) for task in tasks)
    counts_by_owner = Counter(str(task.get("owner", "UNKNOWN")) for task in tasks)
    ready_by_agent: dict[str, list[str]] = defaultdict(list)
    lane_ready: dict[str, list[str]] = defaultdict(list)
    lane_active: dict[str, list[str]] = defaultdict(list)
    stale_unconfirmed: list[dict[str, Any]] = []

    for task in tasks:
        if not isinstance(task, dict):
            continue
        task_id = str(task.get("id", ""))
        owner = str(task.get("owner", "Any"))
        status = str(task.get("status", "UNKNOWN"))
        lanes = classify_lanes(task)
        if status in QUEUE_STATUSES:
            if owner in {"Codex", "Cowork"}:
                ready_by_agent[owner].append(task_id)
            elif owner == "Any":
                ready_by_agent["Codex"].append(task_id)
                ready_by_agent["Cowork"].append(task_id)
            for lane in lanes:
                lane_ready[lane].append(task_id)
        if status in ACTIVE_STATUSES:
            for lane in lanes:
                lane_active[lane].append(task_id)
        delivery_state = str(task.get("delivery_state", "")).upper()
        age = seconds_since(task.get("delivery_unconfirmed_at") or task.get("dispatched_at"))
        if status == "IN_PROGRESS" and "UNCONFIRMED" in delivery_state and age and age > 10 * 60:
            stale_unconfirmed.append(
                {
                    "task_id": task_id,
                    "owner": owner,
                    "delivery_state": delivery_state,
                    "age_minutes": round(age / 60, 1),
                }
            )

    lane_gaps = []
    for lane, meta in LANES.items():
        ready_count = len(lane_ready.get(lane, []))
        if ready_count < int(meta["min_ready"]):
            lane_gaps.append(
                {
                    "lane": lane,
                    "ready_count": ready_count,
                    "minimum_ready": meta["min_ready"],
                    "description": meta["description"],
                }
            )

    history_counts = recent_history_counts()
    seed_suggestions = recommended_seed_tasks(tasks, ready_by_agent)
    recommendations = []
    if not ready_by_agent.get("Codex"):
        recommendations.append("Seed at least one Codex READY implementation/formalization task before running overnight.")
    elif len(ready_by_agent.get("Codex", [])) < CODEX_READY_FLOOR:
        recommendations.append(
            f"Codex READY floor is below {CODEX_READY_FLOOR}; seed concrete lane tasks before long unattended runs."
        )
    if not ready_by_agent.get("Cowork"):
        recommendations.append("Seed at least one Cowork READY creative research or audit task before running overnight.")
    if lane_gaps:
        missing = ", ".join(gap["lane"] for gap in lane_gaps)
        recommendations.append(f"Fill missing work lanes: {missing}.")
    if stale_unconfirmed:
        recommendations.append("Normalize or requeue stale unconfirmed IN_PROGRESS tasks with explicit no-completion evidence.")
    if history_counts["dispatch_meta_task"] > 5:
        if len(ready_by_agent.get("Codex", [])) < CODEX_READY_FLOOR or lane_gaps:
            recommendations.append("META dispatches are high in recent history; seed more concrete READY tasks per lane.")
        else:
            recommendations.append("META dispatches are high in recent history; Codex READY floor is currently satisfied, monitor the next unattended run.")
    if seed_suggestions:
        ids = ", ".join(item["id"] for item in seed_suggestions)
        recommendations.append(f"Suggested deterministic Codex seeds: {ids}.")

    next_tasks = {
        "Codex": state.get("next_task_id"),
        "Cowork": state.get("next_cowork_task_id"),
    }
    codex_ready_ok = len(ready_by_agent.get("Codex", [])) >= CODEX_READY_FLOOR
    cowork_ready_ok = bool(ready_by_agent.get("Cowork"))
    report = {
        "updated_at": utc_now(),
        "status": "OK" if not lane_gaps and codex_ready_ok and cowork_ready_ok else "NEEDS_ATTENTION",
        "strategic_goal": "Unconditional Clay-level Yang-Mills formalization; no Clay claim without full formal evidence.",
        "counts_by_status": dict(counts_by_status),
        "counts_by_owner": dict(counts_by_owner),
        "ready_by_agent": {agent: ids[:10] for agent, ids in ready_by_agent.items()},
        "lane_ready_counts": {lane: len(ids) for lane, ids in lane_ready.items()},
        "lane_active_counts": {lane: len(ids) for lane, ids in lane_active.items()},
        "lane_gaps": lane_gaps,
        "ready_floor": {
            "Codex": CODEX_READY_FLOOR,
            "Cowork": 1,
        },
        "recommended_seed_tasks": seed_suggestions,
        "stale_unconfirmed_in_progress": stale_unconfirmed[:10],
        "recent_history_counts": dict(history_counts),
        "role_rotation": ROLE_ROTATION,
        "next_tasks": next_tasks,
        "recommendations": recommendations,
    }
    return report


def write_playbook() -> None:
    lines = [
        "# Continuous Improvement Playbook",
        "",
        "Purpose: keep Codex and Cowork improving the system every run while preserving mathematical honesty.",
        "",
        "## Daily lanes",
        "",
    ]
    for lane, meta in LANES.items():
        lines.append(f"- `{lane}`: {meta['description']}")
    lines.extend(
        [
            "",
            "## Role rotation",
            "",
        ]
    )
    for role in ROLE_ROTATION:
        lines.append(f"- `{role['role']}` ({role['agent']}): {role['purpose']}")
    lines.extend(
        [
            "",
            "## Guardrails",
            "",
            "- Never move `F3-COUNT` above `CONDITIONAL_BRIDGE` without complete Lean evidence and Cowork audit.",
            "- Never convert creative research into a proof claim without a no-sorry Lean artifact.",
            f"- Every overnight run should have at least {CODEX_READY_FLOOR} concrete READY Codex tasks and one READY Cowork task.",
            "- Every week should include at least one formalization task, one creative research task, one audit task, one automation task, and one planning/metrics task.",
            "",
            "## Ready-floor routine",
            "",
            f"- Treat fewer than {CODEX_READY_FLOOR} Codex READY tasks as a warning even when lane coverage is otherwise green.",
            "- Use `recommended_seed_tasks` from `dashboard/continuous_improvement_status.json` as the deterministic seed list.",
            "- Refresh `SEED_TASK_TEMPLATES` whenever preflight can name fewer than three unused Codex seed suggestions.",
            "- Seed tasks only through an explicit registry update/META task, never as a hidden preflight mutation.",
            "- Keep Cowork polling gates intact; fill Cowork idle time with non-polling creative research or landed-substrate audits.",
        ]
    )
    PLAYBOOK_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    report = build_report()
    REPORT_FILE.parent.mkdir(parents=True, exist_ok=True)
    REPORT_FILE.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    write_playbook()
    print(
        "[OK]" if report["status"] == "OK" else "[!]",
        "Continuous improvement:",
        f"status={report['status']};",
        f"Codex READY={len(report['ready_by_agent'].get('Codex', []))};",
        f"Cowork READY={len(report['ready_by_agent'].get('Cowork', []))};",
        f"lane_gaps={len(report['lane_gaps'])};",
        f"report={REPORT_FILE}",
    )
    if report["recommended_seed_tasks"]:
        print(
            "    - recommended_seed_tasks:",
            ", ".join(item["id"] for item in report["recommended_seed_tasks"]),
        )
    for item in report["recommendations"][:5]:
        print(f"    - {item}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
