from __future__ import annotations

import importlib.util
import json
import re
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tmp" / "verify_eq337_complex_coordinate_evidence.py"
PACKAGER = ROOT / "tmp" / "package_eq337_complex_coordinate_evidence.py"


def load_verifier():
    spec = importlib.util.spec_from_file_location("verify_eq337_evidence", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_packager():
    spec = importlib.util.spec_from_file_location("package_eq337_evidence", PACKAGER)
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
    path = tmp_path / "eq337.ipynb"
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
        f"RUNNER_REV={verifier.RUNNER_REV}",
        "LEAN_AXIOM_READOUT_COVERAGE_OK files=6 declarations=57 readouts=57",
    ]
    lines.extend(f"STAGE={stage} EXIT=0 SECONDS=1.0" for stage in verifier.STAGES)
    for index, declaration in enumerate(expected_declarations(verifier)):
        axioms = "propext, Quot.sound"
        if bad_axiom and index == 0:
            axioms += ", sorryAx"
        lines.append(f"'{declaration}' depends on axioms: [{axioms}]")
    lines.extend(
        (
            "FINAL_STATUS=PASS",
            "LAUNCHER_EXIT=0",
            "EVIDENCE_SHA256=" + "C" * 64,
            "EVIDENCE_ARCHIVE_SHA256=" + "D" * 64,
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


def test_complete_permitted_transcript_passes(tmp_path: Path, monkeypatch) -> None:
    verifier = load_verifier()
    notebook = write_notebook(tmp_path, synthetic_transcript(verifier))
    output = tmp_path / "result.json"
    assert run_main(verifier, monkeypatch, notebook, output) == 0
    result = json.loads(output.read_text(encoding="utf-8"))
    assert result["status"] == "EQ337_COMPLEX_COORDINATE_EVIDENCE_OK"
    assert result["expected_declarations"] == 57


def test_forbidden_axiom_fails(tmp_path: Path, monkeypatch) -> None:
    verifier = load_verifier()
    notebook = write_notebook(tmp_path, synthetic_transcript(verifier, bad_axiom=True))
    with pytest.raises(RuntimeError, match=re.escape("FORBIDDEN_AXIOM=sorryAx")):
        run_main(verifier, monkeypatch, notebook, tmp_path / "result.json")


def test_eq337_evidence_packager_preserves_verified_notebook(
    tmp_path: Path, monkeypatch
) -> None:
    verifier = load_verifier()
    packager = load_packager()
    notebook = write_notebook(tmp_path, synthetic_transcript(verifier))
    destination = tmp_path / "package"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            str(PACKAGER),
            "--notebook",
            str(notebook),
            "--destination",
            str(destination),
        ],
    )
    assert packager.main() == 0
    manifest = json.loads((destination / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["status"] == "EQ337_EVIDENCE_PACKAGE_OK"
    assert manifest["runner_hashes"]["EVIDENCE_SHA256"] == "C" * 64
    assert (destination / "SHA256SUMS").is_file()
