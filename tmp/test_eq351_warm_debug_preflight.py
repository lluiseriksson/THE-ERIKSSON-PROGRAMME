from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts" / "colab_eq351_warm_debug.py"


def load_runner():
    spec = importlib.util.spec_from_file_location("eq351_warm_debug", RUNNER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def write(repo: Path, relative: str, text: str) -> None:
    path = repo / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def row(source: str) -> tuple[str, str, str]:
    stem = source.removesuffix(".lean")
    return stem, source, f".lake/build/lib/lean/{stem}.olean"


def test_preflight_accepts_ordered_closed_tmp_imports(tmp_path: Path) -> None:
    runner = load_runner()
    write(tmp_path, "tmp/A.draft.lean", "/-! PRE-VALIDATION: test. -/\n")
    write(
        tmp_path,
        "tmp/B.draft.lean",
        "import tmp.A.draft\n/-! PRE-VALIDATION: test. -/\n",
    )
    runner.QUEUE = (row("tmp/A.draft.lean"), row("tmp/B.draft.lean"))
    runner.preflight(tmp_path)


def test_preflight_rejects_tmp_import_outside_queue(tmp_path: Path) -> None:
    runner = load_runner()
    write(
        tmp_path,
        "tmp/A.draft.lean",
        "import tmp.Missing.draft\n/-! PRE-VALIDATION: test. -/\n",
    )
    runner.QUEUE = (row("tmp/A.draft.lean"),)
    with pytest.raises(RuntimeError, match="EQ351_WARM_TMP_IMPORT_OUTSIDE_QUEUE"):
        runner.preflight(tmp_path)


def test_preflight_rejects_forward_tmp_import(tmp_path: Path) -> None:
    runner = load_runner()
    write(
        tmp_path,
        "tmp/A.draft.lean",
        "import tmp.B.draft\n/-! PRE-VALIDATION: test. -/\n",
    )
    write(tmp_path, "tmp/B.draft.lean", "/-! PRE-VALIDATION: test. -/\n")
    runner.QUEUE = (row("tmp/A.draft.lean"), row("tmp/B.draft.lean"))
    with pytest.raises(RuntimeError, match="EQ351_WARM_TMP_IMPORT_ORDER"):
        runner.preflight(tmp_path)


def test_preflight_rejects_forbidden_proof_placeholder(tmp_path: Path) -> None:
    runner = load_runner()
    write(
        tmp_path,
        "tmp/A.draft.lean",
        "/-! PRE-VALIDATION: test. -/\ntheorem bad : True := by sorry\n",
    )
    runner.QUEUE = (row("tmp/A.draft.lean"),)
    with pytest.raises(RuntimeError, match="EQ351_WARM_FORBIDDEN_TOKEN"):
        runner.preflight(tmp_path)
