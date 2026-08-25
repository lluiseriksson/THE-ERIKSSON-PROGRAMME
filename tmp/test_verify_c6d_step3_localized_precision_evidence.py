from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import re
import sys

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tmp" / "verify_c6d_step3_localized_precision_evidence.py"


def load_verifier():
    spec = importlib.util.spec_from_file_location("verify_c6d_step3_evidence", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def write_notebook(tmp_path: Path, transcript: str) -> Path:
    path = tmp_path / "step3.ipynb"
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


def synthetic_transcript(verifier, declarations: list[str], source_sha: str) -> str:
    lines = [
        f"RUNNER_REV={verifier.RUNNER_REV}",
        source_sha,
        "LEAN_AXIOM_READOUT_COVERAGE_OK files=6 declarations=11 readouts=11",
    ]
    lines.extend(f"STAGE={stage} EXIT=0 SECONDS=1.0" for stage in verifier.STAGES)
    lines.extend(
        f"'{declaration}' depends on axioms: [propext, Quot.sound]"
        for declaration in declarations
    )
    lines.extend(
        (
            "FINAL_STATUS=PASS",
            "LAUNCHER_EXIT=0",
        )
    )
    return "\n".join(lines) + "\n"


def test_complete_permitted_transcript_passes(tmp_path: Path, monkeypatch) -> None:
    verifier = load_verifier()
    source_sha = "a" * 40
    # Use a deterministic replacement surface without reading a future source commit.
    declarations = [f"YangMills.RG.synthetic_{index}" for index in range(11)]
    by_module: dict[str, list[str]] = {}
    cursor = 0
    for module, count in verifier.BRICKS:
        by_module[module] = declarations[cursor : cursor + count]
        cursor += count

    monkeypatch.setattr(verifier, "exact_commit", lambda _repo, _sha: None)
    def fake_blob(_repo: Path, _sha: str, path: str) -> bytes:
        if path.endswith("Audit.lean"):
            module = Path(path).name.removesuffix("Audit.lean")
            return ("\n".join(f"#print axioms {name}" for name in by_module[module]) + "\n").encode()
        return b"import Mathlib\n"
    monkeypatch.setattr(verifier, "git_blob", fake_blob)

    notebook = write_notebook(
        tmp_path,
        synthetic_transcript(verifier, declarations, source_sha),
    )
    output = tmp_path / "result.json"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            str(SCRIPT),
            "--repo",
            str(ROOT),
            "--source-sha",
            source_sha,
            "--notebook",
            str(notebook),
            "--json-out",
            str(output),
        ],
    )
    assert verifier.main() == 0
    result = json.loads(output.read_text(encoding="utf-8"))
    assert result["status"] == "C6D_STEP3_LOCALIZED_PRECISION_EVIDENCE_OK"
    assert result["expected_declarations"] == 11

    bad = write_notebook(
        tmp_path,
        synthetic_transcript(verifier, declarations, source_sha).replace(
            "[propext, Quot.sound]", "[propext, sorryAx]", 1
        ),
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            str(SCRIPT),
            "--repo",
            str(ROOT),
            "--source-sha",
            source_sha,
            "--notebook",
            str(bad),
        ],
    )
    with pytest.raises(RuntimeError, match=re.escape("C6D_STEP3_FORBIDDEN_AXIOM=sorryAx")):
        verifier.main()
