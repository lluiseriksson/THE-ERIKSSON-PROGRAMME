from __future__ import annotations

import sys
from pathlib import Path

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import surface_remainder_s2_direct_judge as judge  # noqa: E402


def test_closed_forms_reproduce_registered_stress_values() -> None:
    leading, r2, r3, theta3 = judge.closed_forms(arb("2.9"))
    assert leading.overlaps(arb("0.369921288333819 +/- 1e-15"))
    assert r2.overlaps(arb("0.336346633882395 +/- 1e-15"))
    assert r3.overlaps(arb("0.895436036409288 +/- 1e-15"))
    assert theta3.overlaps(arb("2.86406869745028 +/- 1e-14"))


def test_joint_judge_accepts_and_rejects_synthetic_enclosures() -> None:
    delta, t = arb(1)/20, arb("2.9")
    leading, r2, _, _ = judge.closed_forms(t)
    model = leading+r2*delta
    accepted = judge.judge_value(model+arb("0 +/- 0.001"), delta, t)
    rejected = judge.judge_value(model+arb("0 +/- 0.02"), delta, t)
    assert accepted["passed"]
    assert accepted["margin"] > 0
    assert not rejected["passed"]
