from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tmp" / "seal_c6d_step3_localized_precision_prevalidation.py"


def load_sealer():
    spec = importlib.util.spec_from_file_location("seal_c6d_step3", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_remove_prevalidation_block_is_selective() -> None:
    sealer = load_sealer()
    source = (
        "import Mathlib\n\n"
        "/-!\n"
        "PRE-VALIDATION: source present but not compiler-verified.\n"
        "Second marker line to remove.\n\n"
        "Retained module documentation.\n"
        "-/\n\n"
        "theorem kept : True := by trivial\n"
    ).encode()
    sealed = sealer.remove_prevalidation_block(source, "synthetic.lean").decode()
    assert "PRE-VALIDATION:" not in sealed
    assert "Second marker line" not in sealed
    assert "Retained module documentation." in sealed
    assert "theorem kept" in sealed


def test_remove_prevalidation_block_rejects_ambiguity() -> None:
    sealer = load_sealer()
    with pytest.raises(RuntimeError, match="PREVALIDATION_BLOCK_COUNT"):
        sealer.remove_prevalidation_block(b"import Mathlib\n", "missing.lean")
