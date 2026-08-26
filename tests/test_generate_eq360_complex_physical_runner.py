from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "tmp" / "generate_eq360_complex_physical_runner.py"


def load_generator():
    spec = importlib.util.spec_from_file_location("eq360_runner_test", GENERATOR)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_rendered_runner_is_exact_and_fail_closed(monkeypatch) -> None:
    generator = load_generator()
    monkeypatch.setattr(generator, "digest", lambda _sha, _path: "a" * 64)
    rendered = generator.render("1" * 40, "eq360-test-v1")
    compile(rendered, "generated-runner.py", "exec")
    assert "def capturing_run(" in rendered
    assert "raise RuntimeError(\"FIRST_ERROR=\" + stage)" in rendered
    assert "runner.RUNNER_REV = 'eq360-test-v1'" in rendered
    assert "Eq359ComplexClosedPhysicalTowerPair" in rendered
    assert "eq360_complex_physical_root" in rendered


def test_rendered_runner_keeps_four_pair_scope(monkeypatch) -> None:
    generator = load_generator()
    monkeypatch.setattr(generator, "digest", lambda _sha, _path: "b" * 64)
    rendered = generator.render("2" * 40, "eq360-test-v2")
    assert len(generator.MODULES) == 4
    assert sum(expected for _, expected in generator.MODULES) == 28
    for module, expected in generator.MODULES:
        assert repr((module, expected)) in rendered
