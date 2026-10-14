from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "check_oracle_output",
    ROOT / "scripts" / "check_oracle_output.py",
)
assert SPEC and SPEC.loader
checker = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = checker
SPEC.loader.exec_module(checker)


ORACLE = """import YangMillsCore

/-! # Oracle
`#print axioms YangMills.commented_out` inside a doc block is not a command. -/
-- #print axioms YangMills.line_commented
#print axioms YangMills.a
#check YangMills.Data
#print axioms YangMills.b'
#print axioms YangMills.c
"""

GOOD = """'YangMills.a' depends on axioms: [propext, Classical.choice, Quot.sound]
YangMills.Data.{u_1} {V : Type u_1} (dist : V → V → ℝ) :
  Type
'YangMills.b'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'YangMills.c' does not depend on any axioms
"""


def test_accepts_standard_wrapped_axiom_free_and_check_output() -> None:
    errors, stats = checker.check(ORACLE, GOOD)
    assert errors == []
    assert stats == {
        "requested": 3,
        "readouts": 3,
        "standard_axioms_only": 2,
        "axiom_free": 1,
        "nonstandard": 0,
    }


def test_rejects_sorry_and_project_axioms() -> None:
    output = GOOD.replace("[propext, Classical.choice, Quot.sound]", "[propext, sorryAx]")
    errors, _ = checker.check(ORACLE, output)
    assert any("sorryAx" in error for error in errors)

    output = GOOD.replace("Quot.sound]\n'YangMills.c'", "YangMills.myAxiom]\n'YangMills.c'")
    errors, _ = checker.check(ORACLE, output)
    assert any("YangMills.myAxiom" in error for error in errors)


def test_rejects_missing_reordered_and_unexpected_output() -> None:
    missing = GOOD.replace("'YangMills.c' does not depend on any axioms\n", "")
    errors, _ = checker.check(ORACLE, missing)
    assert any("readout count 2" in error for error in errors)

    reordered = ORACLE.replace("#print axioms YangMills.a\n", "") + "#print axioms YangMills.a\n"
    errors, _ = checker.check(reordered, GOOD)
    assert any("expected YangMills.b'" in error for error in errors)

    noisy = GOOD + "oracle_check.lean:9:0: error: unknown constant 'YangMills.d'\n"
    errors, _ = checker.check(ORACLE, noisy)
    assert any("unexpected output line" in error for error in errors)

    no_check = GOOD.replace("YangMills.Data.{u_1} {V : Type u_1} (dist : V → V → ℝ) :\n  Type\n", "")
    errors, _ = checker.check(ORACLE, no_check)
    assert any("`#check` output count 0" in error for error in errors)
