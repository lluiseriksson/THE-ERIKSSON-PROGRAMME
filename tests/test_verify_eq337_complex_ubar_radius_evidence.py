from __future__ import annotations

import ast
import importlib.util
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts" / "colab_eq337_complex_ubar_radius_validation.py"
VERIFIER = ROOT / "tmp" / "verify_eq337_complex_ubar_radius_evidence.py"
PACKAGE = ROOT / "tmp" / "package_eq337_complex_ubar_radius_evidence.py"


def load_verifier():
    spec = importlib.util.spec_from_file_location("eq337_ubar_verifier", VERIFIER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def literal_assignment(tree: ast.Module, name: str):
    matches = [
        node.value
        for node in tree.body
        if isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id == name
    ]
    assert len(matches) == 1
    return ast.literal_eval(matches[0])


def test_verifier_scope_matches_runner_pair_queue() -> None:
    verifier = load_verifier()
    tree = ast.parse(RUNNER.read_text(encoding="utf-8"))
    pairs = literal_assignment(tree, "PAIRS")
    prerequisite = literal_assignment(tree, "PREREQUISITE")
    source_sha = literal_assignment(tree, "SOURCE_SHA")
    runner_revisions = [
        ast.literal_eval(node.value)
        for node in tree.body
        if isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Attribute)
        and isinstance(node.targets[0].value, ast.Name)
        and node.targets[0].value.id == "runner"
        and node.targets[0].attr == "RUNNER_REV"
    ]
    assert tuple(map(tuple, pairs)) == verifier.MODULES
    assert tuple(prerequisite) == verifier.PREREQUISITE
    assert source_sha == verifier.SOURCE_SHA
    assert runner_revisions == [verifier.RUNNER_REV]
    assert len(verifier.STAGES) == 18
    assert verifier.STAGES[-1] == "complex_ubar_radius_promoted_root"
    assert sum(count for _, count in verifier.MODULES) == 53
    assert verifier.PREREQUISITE[1] + sum(
        count for _, count in verifier.MODULES
    ) == 79


def test_evidence_tools_are_syntax_valid() -> None:
    compile(VERIFIER.read_text(encoding="utf-8"), str(VERIFIER), "exec")
    compile(PACKAGE.read_text(encoding="utf-8"), str(PACKAGE), "exec")


def synthetic_notebook(verifier, *, forbidden: bool = False) -> dict:
    transcript = [
        f"RUNNER_REV={verifier.RUNNER_REV}\n",
        "RUNNER_TRANSPORT_SHA256=" + "a" * 64 + "\n",
        'STAGE=head CMD=["git", "rev-parse", "HEAD"]\n',
        verifier.SOURCE_SHA + "\n",
        "STAGE=head EXIT=0 SECONDS=0.01\n",
    ]
    for stage in verifier.STAGES:
        transcript.append(f"STAGE={stage} EXIT=0 SECONDS=1.0\n")
    declarations: list[str] = []
    prerequisite, _ = verifier.PREREQUISITE
    prerequisite_audit = verifier.git_blob(
        ROOT, f"YangMills/RG/{prerequisite}Audit.lean"
    ).decode()
    declarations.extend(verifier.PRINT_RE.findall(prerequisite_audit))
    for module, _ in verifier.MODULES:
        audit = verifier.git_blob(ROOT, f"YangMills/RG/{module}Audit.lean").decode()
        declarations.extend(verifier.PRINT_RE.findall(audit))
    assert len(declarations) == 79
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
    launcher = 'RUNNER_SHA256 = "' + "a" * 64 + '"\n'
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "id": "gate-synthetic",
                "metadata": {},
                "outputs": [{"output_type": "stream", "name": "stdout", "text": transcript}],
                "source": [launcher],
            }
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def test_verifier_and_packager_accept_complete_exact_transcript(tmp_path: Path) -> None:
    verifier = load_verifier()
    notebook = tmp_path / "executed.ipynb"
    notebook.write_text(json.dumps(synthetic_notebook(verifier)), encoding="utf-8")
    verified = subprocess.run(
        [sys.executable, str(VERIFIER), "--repo", str(ROOT), "--notebook", str(notebook)],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert verified.returncode == 0, verified.stderr
    assert "EQ337_COMPLEX_UBAR_RADIUS_EVIDENCE_OK" in verified.stdout
    destination = tmp_path / "package"
    packaged = subprocess.run(
        [
            sys.executable,
            str(PACKAGE),
            "--notebook",
            str(notebook),
            "--destination",
            str(destination),
        ],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert packaged.returncode == 0, packaged.stderr
    manifest = json.loads((destination / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["status"] == "EQ337_COMPLEX_UBAR_RADIUS_PACKAGE_OK"
    assert manifest["source_sha"] == verifier.SOURCE_SHA


def test_verifier_rejects_forbidden_axiom(tmp_path: Path) -> None:
    verifier = load_verifier()
    notebook = tmp_path / "forbidden.ipynb"
    notebook.write_text(
        json.dumps(synthetic_notebook(verifier, forbidden=True)), encoding="utf-8"
    )
    rejected = subprocess.run(
        [sys.executable, str(VERIFIER), "--repo", str(ROOT), "--notebook", str(notebook)],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert rejected.returncode != 0
    assert "FORBIDDEN_AXIOM=sorryAx" in rejected.stderr
