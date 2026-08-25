from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
HELPER = ROOT / "tmp" / "retarget_eq337_complex_ubar_radius_runner.py"
RUNNER = ROOT / "scripts" / "colab_eq337_complex_ubar_radius_validation.py"
COORDINATE_RUNNER = ROOT / "scripts" / "colab_eq337_complex_coordinate_validation.py"


def load_helper():
    spec = importlib.util.spec_from_file_location("eq337_ubar_runner_retarget", HELPER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_current_pin_is_byte_stable() -> None:
    helper = load_helper()
    current = RUNNER.read_text(encoding="utf-8")
    retargeted = helper.retarget(
        current,
        "b1357760890c9551dd9786da0f691d652bf21eda",
        "eq337-complex-ubar-radius-debug-v1",
    )
    assert retargeted == current


def test_accepts_new_source_only_when_boundary_blobs_are_unchanged() -> None:
    helper = load_helper()
    current = RUNNER.read_text(encoding="utf-8")
    retargeted = helper.retarget(
        current,
        "e44b164c59aa289bb1ca2995bc71dfe7e5f58ef9",
        "eq337-complex-ubar-radius-debug-v2",
    )
    assert 'SOURCE_SHA = "e44b164c59aa289bb1ca2995bc71dfe7e5f58ef9"' in retargeted
    assert 'runner.RUNNER_REV = "eq337-complex-ubar-radius-debug-v2"' in retargeted


def test_accepts_coordinate_runner_when_its_six_blobs_are_unchanged() -> None:
    helper = load_helper()
    current = COORDINATE_RUNNER.read_text(encoding="utf-8")
    retargeted = helper.retarget(
        current,
        "e44b164c59aa289bb1ca2995bc71dfe7e5f58ef9",
        "eq337-complex-coordinate-fresh-v5",
    )
    assert 'SOURCE_SHA = "e44b164c59aa289bb1ca2995bc71dfe7e5f58ef9"' in retargeted
    assert 'runner.RUNNER_REV = "eq337-complex-coordinate-fresh-v5"' in retargeted
