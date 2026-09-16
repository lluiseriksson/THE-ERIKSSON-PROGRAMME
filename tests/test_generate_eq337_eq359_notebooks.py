from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
GENERATORS = (
    (
        ROOT / "tmp" / "generate_eq337_closed_physical_recursion_notebook.py",
        "EQ337_CLOSED_RUNNER_SOURCE_PIN_MISMATCH",
    ),
    (
        ROOT / "tmp" / "generate_eq359_complex_one_scale_average_notebook.py",
        "EQ359_RUNNER_SOURCE_PIN_MISMATCH",
    ),
)


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.mark.parametrize("path,_error", GENERATORS)
def test_notebook_launcher_pins_runner_and_retains_runtime(monkeypatch, path, _error) -> None:
    generator = load(path, "notebook_generator_" + path.stem)
    source_sha = "1" * 40
    runner_checkpoint = "2" * 40
    runner_rev = "test-runner-v1"
    runner = (
        f'SOURCE_SHA = "{source_sha}"\n'
        f'runner.RUNNER_REV = "{runner_rev}"\n'
    ).encode()
    monkeypatch.setattr(generator, "require_commit", lambda _sha, _label: None)
    monkeypatch.setattr(generator, "blob", lambda _sha, _path: runner)
    rendered = generator.generate(
        source_sha,
        runner_checkpoint,
        runner_rev,
        retain_runtime=True,
    )
    notebook = json.loads(rendered)
    assert len(notebook["cells"]) == 1
    cell = "".join(notebook["cells"][0]["source"])
    compile(cell, "launcher.py", "exec")
    assert runner_checkpoint in cell
    assert "RUNTIME_RETAINED_FOR_EVIDENCE_DOWNLOAD=1" in cell
    assert "RUNNER_TRANSPORT_HASH_MISMATCH" in cell


@pytest.mark.parametrize("path,error", GENERATORS)
def test_notebook_rejects_wrong_source_pin(monkeypatch, path, error) -> None:
    generator = load(path, "notebook_generator_bad_" + path.stem)
    monkeypatch.setattr(generator, "require_commit", lambda _sha, _label: None)
    monkeypatch.setattr(
        generator,
        "blob",
        lambda _sha, _path: (
            'SOURCE_SHA = "' + "3" * 40 + '"\n'
            'runner.RUNNER_REV = "test-runner-v1"\n'
        ).encode(),
    )
    with pytest.raises(SystemExit, match=error):
        generator.generate("1" * 40, "2" * 40, "test-runner-v1")
