from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]


def load(relative: str, name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CONTRACT = load(
    "tmp/verify_eq351_exponential_adjoint_remainder_contract.py",
    "eq351_evidence_contract",
)
VERIFIER = load(
    "tmp/verify_eq351_exponential_adjoint_remainder_archive.py",
    "eq351_evidence_verifier",
)
SEALER = load(
    "tmp/seal_eq351_exponential_adjoint_remainder_prevalidation.py",
    "eq351_evidence_sealer",
)


class Eq351EvidenceToolingTest(unittest.TestCase):
    def test_exact_module_and_declaration_scope(self) -> None:
        self.assertEqual(len(CONTRACT.MODULES), 4)
        self.assertEqual(sum(count for _, count in CONTRACT.MODULES), 12)

    def test_exact_seal_scope(self) -> None:
        paths = SEALER.paths(CONTRACT)
        self.assertEqual(len(paths), 8)
        self.assertEqual(len(set(paths)), 8)
        self.assertTrue(all(path.startswith("YangMills/RG/") for path in paths))

    def test_pin_policy_matches_terminal_contract(self) -> None:
        self.assertEqual(
            VERIFIER.EXPECTED_MATHLIB,
            "07642720480157414db592fa85b626dafb71355b",
        )
        self.assertEqual(
            VERIFIER.EXPECTED_TOOLCHAIN_ASSET,
            "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e",
        )

    def test_stage_scope_is_finite_and_unique(self) -> None:
        stages = CONTRACT.stages()
        self.assertEqual(len(stages), 11)
        self.assertEqual(len(stages), len(set(stages)))


if __name__ == "__main__":
    unittest.main()
