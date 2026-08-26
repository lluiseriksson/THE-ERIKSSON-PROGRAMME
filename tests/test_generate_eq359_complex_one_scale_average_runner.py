from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "tmp" / "generate_eq359_complex_one_scale_average_runner.py"


def load_generator():
    spec = importlib.util.spec_from_file_location("eq359_runner_test", GENERATOR)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_rendered_runner_archives_exact_stage_stdout(monkeypatch) -> None:
    generator = load_generator()
    monkeypatch.setattr(generator, "digest", lambda _sha, _path: "a" * 64)
    rendered = generator.render("1" * 40, "eq359-test-v1")
    compile(rendered, "generated-runner.py", "exec")
    assert "def capturing_run(" in rendered
    assert '(runner.EVIDENCE / f"{stage}.stdout").write_text' in rendered
    assert "runner.run = capturing_run" in rendered
    assert "runner.RUNNER_REV = 'eq359-test-v1'" in rendered


def test_rendered_runner_keeps_seven_pair_scope(monkeypatch) -> None:
    generator = load_generator()
    monkeypatch.setattr(generator, "digest", lambda _sha, _path: "b" * 64)
    rendered = generator.render("2" * 40, "eq359-test-v2")
    assert len(generator.MODULES) == 7
    assert sum(expected for _, expected in generator.MODULES) == 31
    for module, expected in generator.MODULES:
        assert repr((module, expected)) in rendered
