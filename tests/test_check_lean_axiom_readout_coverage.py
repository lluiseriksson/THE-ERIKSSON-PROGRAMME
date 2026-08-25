from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "check_lean_axiom_readout_coverage.py"


def load_guard():
    spec = importlib.util.spec_from_file_location("check_lean_axiom_readout_coverage", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def write_pair(tmp_path: Path, source: str, audit: str) -> list[Path]:
    source_path = tmp_path / "Source.draft.lean"
    audit_path = tmp_path / "SourceAudit.draft.lean"
    source_path.write_text(source, encoding="utf-8")
    audit_path.write_text(audit, encoding="utf-8")
    return [source_path, audit_path]


def test_exact_public_declaration_coverage(tmp_path: Path) -> None:
    guard = load_guard()
    paths = write_pair(
        tmp_path,
        """/-! def decoy : Nat := 0 -/
def datum : Nat := 1
@[simp] theorem datum_eq : datum = 1 := rfl
private theorem hidden : True := trivial
""",
        """#print axioms datum
#print axioms datum_eq
""",
    )
    assert guard.coverage_failures(paths) == []


def test_missing_readout_fails(tmp_path: Path) -> None:
    guard = load_guard()
    paths = write_pair(tmp_path, "def datum : Nat := 1\n", "")
    assert guard.coverage_failures(paths) == ["MISSING_READOUTS=['datum']"]


def test_unknown_and_duplicate_readouts_fail(tmp_path: Path) -> None:
    guard = load_guard()
    paths = write_pair(
        tmp_path,
        "def datum : Nat := 1\n",
        "#print axioms datum\n#print axioms datum\n#print axioms ghost\n",
    )
    failures = guard.coverage_failures(paths)
    assert "DUPLICATE_READOUTS=['datum']" in failures
    assert "UNKNOWN_READOUTS=['ghost']" in failures


def test_attributes_and_multiline_noncomputable_declaration(tmp_path: Path) -> None:
    guard = load_guard()
    paths = write_pair(
        tmp_path,
        """@[simp]
noncomputable def complexDatum
    : Nat := 1
""",
        "#print axioms complexDatum\n",
    )
    assert guard.coverage_failures(paths) == []
