from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "check_remainder_localization",
    ROOT / "scripts" / "check_remainder_localization.py",
)
assert SPEC and SPEC.loader
checker = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = checker
SPEC.loader.exec_module(checker)


def test_registered_localization_l0_contract() -> None:
    assert checker.R0 == 4
    assert checker.R1 == 10
    assert checker.check() == []


def test_cutoff_is_monotone_on_transition() -> None:
    derivative = checker.sp.factor(checker.sp.diff(checker.smooth, checker.q))
    assert derivative == -30*checker.q**2*(checker.q - 1)**2
