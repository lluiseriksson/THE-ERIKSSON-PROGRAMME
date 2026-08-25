from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
RUNNER_GENERATOR = (
    ROOT / "tmp" / "generate_eq337_complex_forced_recursion_prereq_runner.py"
)
NOTEBOOK_GENERATOR = (
    ROOT / "tmp" / "generate_eq337_complex_forced_recursion_prereq_notebook.py"
)
SMALL_FIELD_SOURCE = (
    ROOT / "tmp" / "BalabanCMP99ComplexUbarSmallFieldPropagation.draft.lean"
)
SOURCE = "a" * 40
REVISION = "complex-recursion-prereq-test-v1"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def worktree_blob(_sha: str, path: str) -> bytes:
    return (ROOT / path).read_bytes().replace(b"\r\n", b"\n")


def generated_runner():
    generator = load(RUNNER_GENERATOR, "complex_recursion_prereq_runner_test")
    generator.require_commit = lambda _sha: None
    generator.blob = worktree_blob
    return generator, generator.render(SOURCE, REVISION)


def test_runner_freezes_the_exact_stop_on_first_error_queue() -> None:
    generator, text = generated_runner()
    compile(text, "generated_complex_recursion_prereq_runner.py", "exec")

    assert len(generator.PATHS) == 5
    assert text.count("'PRE-VALIDATION'") == 0
    assert text.count(".draft.lean") >= 4
    stages = [
        "complex_inverse_radius_repro",
        "complex_recursion_prereq_materialize_dependencies",
        "complex_inverse_radius_source",
        "complex_inverse_radius_audit",
        "complex_ubar_small_field_source",
        "complex_ubar_small_field_audit",
    ]
    offsets = [text.index(f'"{stage}"') for stage in stages]
    assert offsets == sorted(offsets)
    assert "runner.SOURCE_BLOBS" in text
    assert "runner.RUNNER_REV = 'complex-recursion-prereq-test-v1'" in text
    assert "runner.SOURCE_SHA = SOURCE_SHA" in text
    assert "RUNTIME_UNASSIGN_DEFERRED" not in text


def test_runner_rejects_a_missing_prevalidation_marker() -> None:
    generator = load(RUNNER_GENERATOR, "complex_recursion_prereq_tamper_test")
    generator.require_commit = lambda _sha: None
    first = generator.PATHS[0]

    def tampered_blob(sha: str, path: str) -> bytes:
        data = worktree_blob(sha, path)
        if path == first:
            return data.replace(b"PRE-VALIDATION", b"PREVALIDATION", 1)
        return data

    generator.blob = tampered_blob
    with pytest.raises(SystemExit, match="PREVALIDATION_MARKER_MISSING"):
        generator.render(SOURCE, REVISION)


def test_notebook_binds_the_runner_bytes_and_stable_cell_id() -> None:
    _runner_generator, runner = generated_runner()
    generator = load(NOTEBOOK_GENERATOR, "complex_recursion_prereq_notebook_test")
    generator.require_commit = lambda _sha, _label: None
    generator.blob = lambda _sha, path: (
        runner.encode()
        if path == generator.RUNNER_PATH
        else (_ for _ in ()).throw(AssertionError(path))
    )

    notebook = json.loads(generator.generate(SOURCE, "b" * 40, REVISION))
    assert len(notebook["cells"]) == 1
    cell = notebook["cells"][0]
    digest = hashlib.sha256(runner.encode()).hexdigest()
    assert cell["id"] == f"gate-{digest[:16]}"
    launcher = "".join(cell["source"])
    assert f'RUNNER_SHA256 = "{digest}"' in launcher
    assert "/" + "b" * 40 + "/" + generator.RUNNER_PATH in launcher
    assert "if measured != RUNNER_SHA256" in launcher
    assert "release_runtime()" in launcher


def test_small_field_radius_keeps_both_physical_costs_literal() -> None:
    text = SMALL_FIELD_SOURCE.read_text(encoding="utf-8")
    start = text.index("def cmp99SourceComplexUbarNextLinkRadius")
    end = text.index("\n\n/-- Radius on both orientations", start)
    definition = text[start:end]
    assert "cmp99UbarExpRadius B * (1 + r) ^ M" in definition
    assert "+\n    (M : ℝ) * r * (1 + r) ^ M" in definition

    start = text.index("def cmp99SourceComplexUbarNextOrientedLinkRadius")
    end = text.index("\n\nvariable {d M N'", start)
    oriented = text[start:end]
    assert "let q := cmp99SourceComplexUbarNextLinkRadius M r B" in oriented
    assert "q / (1 - q)" in oriented


def test_source_facing_step_discharges_deviation_internally() -> None:
    text = SMALL_FIELD_SOURCE.read_text(encoding="utf-8")
    name = "noncomputable def cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius"
    start = text.index(name)
    body_start = text.index(":\n    GaugeConfig", start)
    signature = text[start:body_start]
    assert "(hdev" not in signature
    assert "(background" in signature
    assert "(hnoWinding" in signature

    body_end = text.index("\n\n/-- The generic source step internally", body_start)
    body = text[body_start:body_end]
    assert "let B := cmp99SourceComplexUbarNoWindingBudget" in body
    assert "exact cmp99SourceComplexLocalizedNextBackground background B (by" in body
    assert (
        "norm_cmp99SourceComplexLocalizedUbarDeviation_le_uniformRadius_of_linkRadius"
        in body
    )


def test_negative_orientation_pays_the_complex_inverse_radius() -> None:
    text = SMALL_FIELD_SOURCE.read_text(encoding="utf-8")
    start = text.index(
        "theorem norm_cmp99SourceComplexLocalizedNextBackground_sub_one_le"
    )
    end = text.index("\n\n/-- One generic complex source RG step", start)
    theorem = text[start:end]
    assert "(hq1 : cmp99SourceComplexUbarNextLinkRadius M r B < 1)" in theorem
    assert "norm_cmp99SpecialLinear_inv_sub_one_le_div" in theorem
    assert "norm_cmp99SourceComplexLocalizedNextBackground_apply_pos_sub_one_le" in theorem
