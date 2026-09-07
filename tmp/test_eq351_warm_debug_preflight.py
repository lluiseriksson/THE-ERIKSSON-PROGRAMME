from __future__ import annotations

import importlib.util
from pathlib import Path
import subprocess

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
    output = ".lake/build/lib/lean/" + stem.replace(".", "/") + ".olean"
    return stem, source, output


def git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    ).stdout.strip()


def initialize_git(repo: Path) -> str:
    git(repo, "init")
    git(repo, "config", "user.email", "test@example.invalid")
    git(repo, "config", "user.name", "Eq351 Test")
    write(repo, "YangMills/A.lean", "def a : Nat := 1\n")
    git(repo, "add", "YangMills/A.lean")
    git(repo, "commit", "-m", "base")
    return git(repo, "rev-parse", "HEAD")


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


def test_preflight_rejects_module_incompatible_output_path(tmp_path: Path) -> None:
    runner = load_runner()
    write(tmp_path, "tmp/A.draft.lean", "/-! PRE-VALIDATION: test. -/\n")
    runner.QUEUE = (
        (
            "bad_output",
            "tmp/A.draft.lean",
            ".lake/build/lib/lean/tmp/A.draft.olean",
        ),
    )
    with pytest.raises(RuntimeError, match="EQ351_WARM_OUTPUT_PATH_MISMATCH"):
        runner.preflight(tmp_path)


def test_cache_base_accepts_changed_project_source_in_queue(tmp_path: Path) -> None:
    runner = load_runner()
    base = initialize_git(tmp_path)
    write(tmp_path, "YangMills/A.lean", "def a : Nat := 2\n")
    git(tmp_path, "add", "YangMills/A.lean")
    git(tmp_path, "commit", "-m", "change queued source")
    runner.QUEUE = (row("YangMills/A.lean"),)
    runner.cache_base_preflight(tmp_path, base)


def test_cache_base_rejects_changed_project_source_outside_queue(
    tmp_path: Path,
) -> None:
    runner = load_runner()
    base = initialize_git(tmp_path)
    write(tmp_path, "YangMills/Outside.lean", "def outside : Nat := 1\n")
    git(tmp_path, "add", "YangMills/Outside.lean")
    git(tmp_path, "commit", "-m", "change outside queue")
    runner.QUEUE = (row("YangMills/A.lean"),)
    with pytest.raises(
        RuntimeError, match="EQ351_WARM_CHANGED_PROJECT_SOURCE_OUTSIDE_QUEUE"
    ):
        runner.cache_base_preflight(tmp_path, base)
