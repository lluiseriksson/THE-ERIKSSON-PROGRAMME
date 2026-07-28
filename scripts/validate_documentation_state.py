"""Keep public front doors aligned with the canonical proof-state contract."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
FRONT_DOORS = (
    "README.md",
    "CURRENT-STATE.md",
    "ROADMAP.md",
    "HORIZON.md",
    "HYPOTHESIS_FRONTIER.md",
    "README-FOR-NEXT-MODEL.md",
    "SATELLITES.md",
)
SUBJECTIVE_PERCENT = re.compile(r"(?<![0-9])(?:3|15|25|58|76|94|98|99)%")
MOVING_HEAD_AS_CHECKPOINT = re.compile(
    r"current\s+`?origin/main`?[^\n]{0,80}(?:source|Lean)\s+checkpoint",
    re.IGNORECASE,
)


def _load_json(path: Path, label: str, errors: list[str]) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        errors.append(f"{label}: file does not exist")
    except json.JSONDecodeError as exc:
        errors.append(f"{label}: invalid JSON: {exc}")
    return None


def validate_documentation(root: Path = ROOT) -> list[str]:
    errors: list[str] = []
    state = _load_json(root / "project-state.json", "project-state.json", errors)
    checkpoint = None
    if isinstance(state, dict):
        core = state.get("lean_core")
        if isinstance(core, dict):
            checkpoint = core.get("source_checkpoint")
    if not isinstance(checkpoint, str) or not checkpoint:
        errors.append("project-state.json: missing lean_core.source_checkpoint")

    for relative in FRONT_DOORS:
        path = root / relative
        if not path.is_file():
            errors.append(f"{relative}: file does not exist")
            continue
        text = path.read_text(encoding="utf-8")
        if "project-state.json" not in text:
            errors.append(f"{relative}: missing canonical project-state.json link")
        if SUBJECTIVE_PERCENT.search(text):
            errors.append(f"{relative}: contains a non-canonical completion percentage")
        if MOVING_HEAD_AS_CHECKPOINT.search(text):
            errors.append(f"{relative}: presents moving origin/main as the Lean checkpoint")

    dashboard = _load_json(
        root / "docs" / "dashboard" / "data.json", "docs/dashboard/data.json", errors
    )
    if isinstance(dashboard, dict):
        meta = dashboard.get("meta")
        if not isinstance(meta, dict) or "project-state.json" not in str(meta.get("state", "")):
            errors.append("docs/dashboard/data.json: meta.state must link project-state.json")
        milestones = dashboard.get("milestones")
        if not isinstance(milestones, list):
            errors.append("docs/dashboard/data.json: milestones must be a list")
        else:
            for milestone in milestones:
                if isinstance(milestone, dict) and "pct" in milestone:
                    errors.append(
                        f"docs/dashboard/data.json: milestone {milestone.get('id')} uses pct"
                    )
            m3 = next(
                (m for m in milestones if isinstance(m, dict) and m.get("id") == "M3"),
                None,
            )
            if not isinstance(m3, dict) or m3.get("display") != "CONDITIONAL":
                errors.append("docs/dashboard/data.json: M3 must display CONDITIONAL")

    return errors


def main() -> int:
    errors = validate_documentation()
    if errors:
        print(f"documentation state validation: {len(errors)} problem(s)")
        for error in errors:
            print(f"  - {error}")
        return 1
    print("documentation state validation OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
