from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tmp" / "verify_eq351_exponential_adjoint_remainder_contract.py"
SPEC = importlib.util.spec_from_file_location("eq351_contract", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
CONTRACT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CONTRACT)


class Eq351ContractTest(unittest.TestCase):
    def test_declaration_total_is_eight(self) -> None:
        self.assertEqual(sum(count for _, count in CONTRACT.MODULES), 8)

    def test_stage_order_is_finite_and_exact(self) -> None:
        stages = CONTRACT.stages()
        self.assertEqual(len(stages), 9)
        self.assertEqual(stages[0], "eq351_materialize_dependencies")
        self.assertEqual(stages[-1], "eq351_root")
        self.assertEqual(len(set(stages)), len(stages))

    def test_axiom_policy(self) -> None:
        self.assertEqual(
            CONTRACT.ALLOWED,
            {"propext", "Classical.choice", "Quot.sound"},
        )
        self.assertEqual(CONTRACT.FORBIDDEN, {"sorryAx", "ofReduceBool"})


if __name__ == "__main__":
    unittest.main()
