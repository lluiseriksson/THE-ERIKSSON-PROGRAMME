from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "tmp" / "generate_eq337_closed_physical_recursion_runner.py"


def load_generator():
    spec = importlib.util.spec_from_file_location("eq337_closed_runner_test", GENERATOR)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_rendered_runner_archives_exact_stage_stdout(monkeypatch) -> None:
    generator = load_generator()
    monkeypatch.setattr(generator, "digest", lambda _sha, _path: "a" * 64)
    rendered = generator.render("1" * 40, "closed-physical-test-v1")
    compile(rendered, "generated-runner.py", "exec")
    assert "def capturing_run(" in rendered
    assert '(runner.EVIDENCE / f"{stage}.stdout").write_text' in rendered
    assert 'runner.run = capturing_run' in rendered
    assert 'runner.RUNNER_REV = \'closed-physical-test-v1\'' in rendered


def test_rendered_runner_keeps_three_pair_scope(monkeypatch) -> None:
    generator = load_generator()
    monkeypatch.setattr(generator, "digest", lambda _sha, _path: "b" * 64)
    rendered = generator.render("2" * 40, "closed-physical-test-v2")
    assert len(generator.MODULES) == 3
    for module, expected in generator.MODULES:
        assert repr((module, expected)) in rendered
