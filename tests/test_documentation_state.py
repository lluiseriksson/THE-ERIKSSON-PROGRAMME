from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_documentation_state",
    ROOT / "scripts" / "validate_documentation_state.py",
)
assert SPEC and SPEC.loader
validator = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = validator
SPEC.loader.exec_module(validator)


def documentation_fixture(root: Path) -> None:
    (root / "docs" / "dashboard").mkdir(parents=True)
    (root / "project-state.json").write_text(
        json.dumps({"lean_core": {"source_checkpoint": "abcdef0"}}),
        encoding="utf-8",
    )
    for relative in validator.FRONT_DOORS:
        (root / relative).write_text(
            "Canonical state: project-state.json; recorded checkpoint abcdef0.\n",
            encoding="utf-8",
        )
    (root / "docs" / "dashboard" / "data.json").write_text(
        json.dumps(
            {
                "meta": {"state": "https://example.invalid/project-state.json"},
                "milestones": [
                    {"id": "M0", "display": "PROVED"},
                    {"id": "M3", "display": "CONDITIONAL"},
                ],
            }
        ),
        encoding="utf-8",
    )


def test_repository_documentation_state_is_valid() -> None:
    assert validator.validate_documentation(ROOT) == []


def test_valid_documentation_fixture(tmp_path: Path) -> None:
    documentation_fixture(tmp_path)
    assert validator.validate_documentation(tmp_path) == []


def test_subjective_completion_percentage_is_rejected(tmp_path: Path) -> None:
    documentation_fixture(tmp_path)
    (tmp_path / "README.md").write_text(
        "Canonical: project-state.json. M3 is 94% complete.\n", encoding="utf-8"
    )
    errors = validator.validate_documentation(tmp_path)
    assert any("non-canonical completion percentage" in error for error in errors)


def test_moving_main_cannot_be_presented_as_checkpoint(tmp_path: Path) -> None:
    documentation_fixture(tmp_path)
    (tmp_path / "CURRENT-STATE.md").write_text(
        "Canonical: project-state.json. Current `origin/main` is source checkpoint abcdef0.\n",
        encoding="utf-8",
    )
    errors = validator.validate_documentation(tmp_path)
    assert any("moving origin/main" in error for error in errors)


def test_dashboard_percentage_and_m3_promotion_are_rejected(tmp_path: Path) -> None:
    documentation_fixture(tmp_path)
    path = tmp_path / "docs" / "dashboard" / "data.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    data["milestones"][1] = {"id": "M3", "display": "PROVED", "pct": 100}
    path.write_text(json.dumps(data), encoding="utf-8")
    errors = validator.validate_documentation(tmp_path)
    assert any("milestone M3 uses pct" in error for error in errors)
    assert any("M3 must display CONDITIONAL" in error for error in errors)
