from __future__ import annotations

import importlib.util
import json
import re
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tmp" / "verify_c6d_root_transitive_axioms.py"


def load_verifier():
    spec = importlib.util.spec_from_file_location("verify_c6d_root_axioms", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def expected_declarations(verifier) -> list[str]:
    names: list[str] = []
    for module in verifier.MODULES:
        audit = verifier.git_blob(
            ROOT, f"YangMills/RG/{module}Audit.lean"
        ).decode("utf-8")
        names.extend(verifier.PRINT_RE.findall(audit))
    return names


def write_notebook(tmp_path: Path, transcript: str) -> Path:
    path = tmp_path / "c6d.ipynb"
    path.write_text(
        json.dumps(
            {
                "cells": [
                    {
                        "cell_type": "code",
                        "outputs": [{"output_type": "stream", "text": [transcript]}],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    return path


def synthetic_transcript(verifier, bad_axiom: bool = False) -> str:
    lines = [
        'STAGE=c6d_localized_retained_tower_root CMD=["lake", "build", "YangMillsCore"]'
    ]
    for index, declaration in enumerate(expected_declarations(verifier)):
        axioms = "propext, Quot.sound"
        if bad_axiom and index == 0:
            axioms += ", sorryAx"
        lines.append(f"'{declaration}' depends on axioms: [{axioms}]")
    lines.extend(
        (
            "Build completed successfully (1 jobs)",
            "STAGE=c6d_localized_retained_tower_root EXIT=0 SECONDS=1.0",
            "FINAL_STATUS=PASS",
            "LAUNCHER_EXIT=0",
        )
    )
    return "\n".join(lines) + "\n"


def run_main(verifier, monkeypatch, notebook: Path, output: Path) -> int:
    monkeypatch.setattr(
        sys,
        "argv",
        [
            str(SCRIPT),
            "--repo",
            str(ROOT),
            "--notebook",
            str(notebook),
            "--json-out",
            str(output),
        ],
    )
    return verifier.main()


def test_complete_root_transcript_passes(tmp_path: Path, monkeypatch) -> None:
    verifier = load_verifier()
    notebook = write_notebook(tmp_path, synthetic_transcript(verifier))
    output = tmp_path / "result.json"
    assert run_main(verifier, monkeypatch, notebook, output) == 0
    result = json.loads(output.read_text(encoding="utf-8"))
    assert result["status"] == "C6D_ROOT_TRANSITIVE_AXIOMS_OK"
    assert result["expected_declarations"] == 92


def test_root_forbidden_axiom_fails(tmp_path: Path, monkeypatch) -> None:
    verifier = load_verifier()
    notebook = write_notebook(tmp_path, synthetic_transcript(verifier, bad_axiom=True))
    with pytest.raises(RuntimeError, match=re.escape("FORBIDDEN_AXIOM=sorryAx")):
        run_main(verifier, monkeypatch, notebook, tmp_path / "result.json")
