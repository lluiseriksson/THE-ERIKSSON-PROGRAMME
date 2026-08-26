from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "tmp" / "generate_eq337_covariant_derivative_runner.py"


def load_generator():
    spec = importlib.util.spec_from_file_location("eq337_derivative_runner_test", GENERATOR)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_rendered_runner_has_exact_three_pair_scope(monkeypatch) -> None:
    generator = load_generator()
    monkeypatch.setattr(generator, "digest", lambda _sha, _path: "a" * 64)
    monkeypatch.setattr(generator, "blob", lambda _sha, _path: b"PRE-VALIDATION:")
    rendered = generator.render("1" * 40, "eq337-derivative-test-v1")
    compile(rendered, "generated-eq337-derivative-runner.py", "exec")
    assert len(generator.MODULES) == 3
    assert sum(expected for _, expected in generator.MODULES) == 57
    assert "def capturing_run(" in rendered
    assert 'runner.RUNNER_REV = \'eq337-derivative-test-v1\'' in rendered
    assert "eq337_covariant_derivative_root" in rendered


def test_rendered_runner_rejects_missing_prevalidation(monkeypatch) -> None:
    generator = load_generator()
    monkeypatch.setattr(generator, "digest", lambda _sha, _path: "b" * 64)
    monkeypatch.setattr(generator, "blob", lambda _sha, _path: b"sealed")
    try:
        generator.render("2" * 40, "eq337-derivative-test-v2")
    except RuntimeError as exc:
        assert "PREVALIDATION_MARKER_MISSING" in str(exc)
    else:
        raise AssertionError("missing PRE-VALIDATION marker was accepted")
