from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tmp" / "promote_eq351_exponential_adjoint_remainder_compiler_gate.py"
SPEC = importlib.util.spec_from_file_location("eq351_promoter", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PROMOTER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROMOTER)


class Eq351PromotionTest(unittest.TestCase):
    def test_scope_is_exact(self) -> None:
        selected = PROMOTER.paths()
        self.assertEqual(len(selected), 6)
        self.assertEqual(len(set(selected)), 6)
        self.assertTrue(all(path.startswith("tmp/") for path in selected))

    def test_destination_strips_draft_suffix(self) -> None:
        self.assertEqual(
            PROMOTER.destination(
                "tmp/BalabanCMP99Eq351ExponentialAdjointRemainder.draft.lean"
            ),
            "YangMills/RG/BalabanCMP99Eq351ExponentialAdjointRemainder.lean",
        )

    def test_retarget_imports_keeps_mark_and_removes_tmp(self) -> None:
        data = (
            b"import tmp.BalabanCMP99Eq351ExponentialAdjointRemainder.draft\n"
            b"/-! PRE-VALIDATION: source is not compiler verified. -/\n"
        )
        actual = PROMOTER.retarget_imports(data)
        self.assertIn(
            b"import YangMills.RG.BalabanCMP99Eq351ExponentialAdjointRemainder",
            actual,
        )
        self.assertNotIn(b"import tmp.", actual)

    def test_retarget_imports_rejects_placeholder(self) -> None:
        data = b"/-! PRE-VALIDATION: not verified. -/\ntheorem bad : True := by\n  sorry\n"
        with self.assertRaisesRegex(RuntimeError, "FORBIDDEN_PLACEHOLDER"):
            PROMOTER.retarget_imports(data)

    def test_core_imports_only_two_audits(self) -> None:
        actual = PROMOTER.core_with_audits(b"import YangMills.RG.Base\n", PROMOTER.paths())
        self.assertEqual(actual.count(b"Audit\n"), 3)


if __name__ == "__main__":
    unittest.main()
