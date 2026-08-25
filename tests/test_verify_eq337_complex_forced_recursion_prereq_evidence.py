from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = (
    ROOT / "tmp" / "verify_eq337_complex_forced_recursion_prereq_evidence.py"
)
PACKAGER = (
    ROOT / "tmp" / "package_eq337_complex_forced_recursion_prereq_evidence.py"
)
REVISION = "complex-recursion-prereq-evidence-test-v1"
RUNNER_HASH = "a" * 64


def load_verifier():
    spec = importlib.util.spec_from_file_location(
        "complex_recursion_prereq_evidence_test", VERIFIER
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
    ).strip()


def synthetic_notebook(verifier, source_sha: str, *, forbidden: bool = False) -> dict:
    transcript = [
        f"RUNNER_REV={REVISION}\n",
        f"RUNNER_TRANSPORT_SHA256={RUNNER_HASH}\n",
        'STAGE=head CMD=["git", "rev-parse", "HEAD"]\n',
        source_sha + "\n",
        "STAGE=head EXIT=0 SECONDS=0.01\n",
    ]
    for stage in verifier.STAGES:
        transcript.append(f"STAGE={stage} EXIT=0 SECONDS=1.0\n")
    for path in verifier.SOURCE_PATHS:
        digest = hashlib.sha256(verifier.git_blob(ROOT, source_sha, path)).hexdigest()
        transcript.append(f"SOURCE_BLOB={path} SHA256={digest}\n")

    declarations: list[str] = []
    for module, _ in verifier.MODULES:
        audit_path = f"tmp/{module}Audit.draft.lean"
        audit = verifier.git_blob(ROOT, source_sha, audit_path).decode()
        declarations.extend(verifier.PRINT_RE.findall(audit))
    assert len(declarations) == 13
    for index, declaration in enumerate(declarations):
        axioms = "sorryAx" if forbidden and index == 0 else "propext, Quot.sound"
        transcript.append(f"'{declaration}' depends on axioms: [{axioms}]\n")
    transcript.extend(
        [
            "EVIDENCE_SHA256=" + "b" * 64 + "\n",
            "EVIDENCE_ARCHIVE_SHA256=" + "c" * 64 + "\n",
            "FINAL_STATUS=PASS\n",
            "LAUNCHER_EXIT=0\n",
        ]
    )
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "id": "gate-synthetic",
                "metadata": {},
                "outputs": [
                    {"output_type": "stream", "name": "stdout", "text": transcript}
                ],
                "source": [f'RUNNER_SHA256 = "{RUNNER_HASH}"\n'],
            }
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def verify(notebook: Path, source_sha: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(VERIFIER),
            "--repo",
            str(ROOT),
            "--notebook",
            str(notebook),
            "--source-sha",
            source_sha,
            "--runner-rev",
            REVISION,
        ],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def test_verifier_accepts_the_complete_exact_transcript(tmp_path: Path) -> None:
    verifier = load_verifier()
    source_sha = head()
    notebook = tmp_path / "executed.ipynb"
    notebook.write_text(
        json.dumps(synthetic_notebook(verifier, source_sha)), encoding="utf-8"
    )
    result = verify(notebook, source_sha)
    assert result.returncode == 0, result.stderr
    payload = json.loads(result.stdout)
    assert payload["status"] == "EQ337_COMPLEX_RECURSION_PREREQ_EVIDENCE_OK"
    assert payload["source_sha"] == source_sha
    assert payload["expected_declarations"] == 13


def test_packager_binds_the_verified_notebook_and_runner_hashes(
    tmp_path: Path,
) -> None:
    verifier = load_verifier()
    source_sha = head()
    notebook = tmp_path / "executed.ipynb"
    notebook.write_text(
        json.dumps(synthetic_notebook(verifier, source_sha)), encoding="utf-8"
    )
    destination = tmp_path / "package"
    packaged = subprocess.run(
        [
            sys.executable,
            str(PACKAGER),
            "--notebook",
            str(notebook),
            "--destination",
            str(destination),
            "--source-sha",
            source_sha,
            "--runner-rev",
            REVISION,
        ],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert packaged.returncode == 0, packaged.stderr
    manifest = json.loads((destination / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["status"] == "EQ337_COMPLEX_RECURSION_PREREQ_PACKAGE_OK"
    assert manifest["source_sha"] == source_sha
    assert manifest["runner_revision"] == REVISION
    assert manifest["runner_hashes"] == {
        "EVIDENCE_SHA256": "B" * 64,
        "EVIDENCE_ARCHIVE_SHA256": "C" * 64,
    }
    assert (destination / "SHA256SUMS").is_file()


def test_verifier_rejects_a_forbidden_axiom(tmp_path: Path) -> None:
    verifier = load_verifier()
    source_sha = head()
    notebook = tmp_path / "forbidden.ipynb"
    notebook.write_text(
        json.dumps(synthetic_notebook(verifier, source_sha, forbidden=True)),
        encoding="utf-8",
    )
    result = verify(notebook, source_sha)
    assert result.returncode != 0
    assert "FORBIDDEN_AXIOM=sorryAx" in result.stderr


def test_verifier_rejects_a_missing_boundary_hash(tmp_path: Path) -> None:
    verifier = load_verifier()
    source_sha = head()
    payload = synthetic_notebook(verifier, source_sha)
    outputs = payload["cells"][0]["outputs"][0]["text"]
    first = verifier.SOURCE_PATHS[0]
    outputs[:] = [line for line in outputs if not line.startswith(f"SOURCE_BLOB={first} ")]
    notebook = tmp_path / "missing-blob.ipynb"
    notebook.write_text(json.dumps(payload), encoding="utf-8")
    result = verify(notebook, source_sha)
    assert result.returncode != 0
    assert f"MARKER_COUNT='SOURCE_BLOB={first}" in result.stderr
