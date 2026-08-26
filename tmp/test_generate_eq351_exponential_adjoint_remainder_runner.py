from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tmp" / "generate_eq351_exponential_adjoint_remainder_runner.py"
SOURCE_SHA = "3ba3875b01b3c6163e1a1b78f599d98cb1ecb6d5"
RUNNER_REV = "eq351-exponential-adjoint-remainder-cold-v3"
SPEC = importlib.util.spec_from_file_location("eq351_runner_generator", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)


class Eq351RunnerGeneratorTest(unittest.TestCase):
    def test_exact_module_scope(self) -> None:
        self.assertEqual(
            GENERATOR.MODULES,
            (
                ("BalabanCMP99Eq337PhysicalRealPerturbationDomain", 7),
                ("BalabanCMP99Eq337PhysicalComplexPerturbationDomain", 1),
                ("BalabanCMP99Eq351PhysicalComplexOrientedPerturbation", 4),
                ("BalabanCMP99Eq351ExponentialAdjointRemainder", 4),
                ("BalabanCMP99Eq351ExponentialAdjointRemainderBound", 3),
            ),
        )

    def test_rendered_runner_is_valid_python(self) -> None:
        rendered = GENERATOR.render(SOURCE_SHA, RUNNER_REV)
        compile(rendered, "eq351-rendered-runner", "exec")

    def test_rendered_runner_carries_exact_pins(self) -> None:
        rendered = GENERATOR.render(SOURCE_SHA, RUNNER_REV)
        self.assertIn(f"SOURCE_SHA = {SOURCE_SHA!r}", rendered)
        self.assertIn(f"runner.RUNNER_REV = {RUNNER_REV!r}", rendered)
        self.assertIn('newline="\\n"', rendered)


if __name__ == "__main__":
    unittest.main()
