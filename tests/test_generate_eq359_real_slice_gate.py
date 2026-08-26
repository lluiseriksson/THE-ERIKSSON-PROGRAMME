from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "tmp" / "generate_eq359_real_slice_runner.py"
NOTEBOOK = ROOT / "tmp" / "generate_eq359_real_slice_notebook.py"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_runner_has_exact_five_pair_scope(monkeypatch):
    generator = load(RUNNER, "eq359_real_slice_runner_test")
    monkeypatch.setattr(generator, "digest", lambda _sha, _path: "a" * 64)
    rendered = generator.render("1" * 40, "eq359-real-slice-test-v1")
    compile(rendered, "generated-eq359-real-slice-runner.py", "exec")
    assert len(generator.MODULES) == 5
    assert sum(expected for _, expected in generator.MODULES) == 23
    assert "eq359_real_slice_root" in rendered
    assert "runner.RUNNER_REV = 'eq359-real-slice-test-v1'" in rendered


def test_runner_hashes_exact_sources_audits_and_core(monkeypatch):
    generator = load(RUNNER, "eq359_real_slice_hash_test")
    seen = []

    def fake_digest(_sha, path):
        seen.append(path)
        return "b" * 64

    monkeypatch.setattr(generator, "digest", fake_digest)
    generator.render("2" * 40, "eq359-real-slice-test-v2")
    assert seen.count("YangMillsCore.lean") == 1
    assert len(seen) == 1 + 2 * len(generator.MODULES) + 1
    assert generator.BASE_RUNNER in seen


def test_notebook_wrapper_pins_real_slice_runner_path():
    generator = load(NOTEBOOK, "eq359_real_slice_notebook_test")
    assert generator.RUNNER_PATH == "scripts/colab_eq359_real_slice_validation.py"
    assert generator.OUTPUT.name == "colab_eq359_real_slice_validation.ipynb"
