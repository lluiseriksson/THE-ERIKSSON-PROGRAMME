from __future__ import annotations

import ast
import importlib.util
from pathlib import Path


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
    assert source_sha == verifier.SOURCE_SHA
    assert runner_revisions == [verifier.RUNNER_REV]
    assert len(verifier.STAGES) == 16
    assert sum(count for _, count in verifier.MODULES) == 52


def test_evidence_tools_are_syntax_valid() -> None:
    compile(VERIFIER.read_text(encoding="utf-8"), str(VERIFIER), "exec")
    compile(PACKAGE.read_text(encoding="utf-8"), str(PACKAGE), "exec")
