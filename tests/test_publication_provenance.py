from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "check_publication_provenance",
    ROOT / "scripts" / "check_publication_provenance.py",
)
assert SPEC and SPEC.loader
guard = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = guard
SPEC.loader.exec_module(guard)


def write_root_pins(root: Path) -> None:
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.29.0-rc6\n", encoding="utf-8")
    (root / "lake-manifest.json").write_text(
        json.dumps(
            {
                "packages": [
                    {
                        "name": "mathlib",
                        "rev": "07642720480157414db592fa85b626dafb71355b",
                    }
                ]
            }
        ),
        encoding="utf-8",
    )


def test_repository_publication_provenance_is_valid() -> None:
    assert guard.validate_repository(ROOT) == []


def test_spatial_osline_placeholders_are_rejected(tmp_path: Path) -> None:
    target = tmp_path / "papers" / "spatial-reconstruction"
    target.mkdir(parents=True)
    (target / "paper.tex").write_text(
        "\\osline{SpatialReconstruction}{DEFLINE}{definiteness}\n"
        "\\osline{SpatialReconstruction}{SITENNVEC}{nonneg}\n",
        encoding="utf-8",
    )
    errors = guard.placeholder_errors(tmp_path, ("papers/spatial-reconstruction",))
    assert len(errors) == 2
    assert any("DEFLINE" in error for error in errors)
    assert any("SITENNVEC" in error for error in errors)


def test_exhaustive_spatial_inventory_is_machine_readable() -> None:
    inventory = json.loads(
        (ROOT / "docs" / "audit-artifacts" / "52-spatial-placeholder-inventory.json")
        .read_text(encoding="utf-8")
    )
    items = inventory["items"]
    assert len(items) == 32
    assert len({item["token"] for item in items}) == 32
    assert sum(item["kind"] == "osline" for item in items) == 20
    assert all(item["status"] == "unverified_for_publication" for item in items)


def test_guard_rejects_every_inventoried_placeholder(tmp_path: Path) -> None:
    inventory = json.loads(
        (ROOT / "docs" / "audit-artifacts" / "52-spatial-placeholder-inventory.json")
        .read_text(encoding="utf-8")
    )
    lines = []
    for item in inventory["items"]:
        token = item["token"]
        if item["kind"] == "osline":
            lines.append(f"\\osline{{SpatialReconstruction}}{{{token}}}{{decl}}")
        else:
            lines.append(f"quantity & {token} \\\\ % @@{token}@@")
    target = tmp_path / "papers" / "spatial-reconstruction"
    target.mkdir(parents=True)
    (target / "paper.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")
    errors = guard.placeholder_errors(tmp_path, ("papers/spatial-reconstruction",))
    assert len(errors) == 32


def test_unfilled_counter_cell_is_rejected_but_stable_marker_is_allowed(
    tmp_path: Path,
) -> None:
    target = tmp_path / "papers" / "spatial-reconstruction"
    target.mkdir(parents=True)
    tex = target / "paper.tex"
    tex.write_text(
        "Full build & JOBSAFTER jobs \\\\ % @@JOBSAFTER@@\n",
        encoding="utf-8",
    )
    assert guard.placeholder_errors(tmp_path, ("papers/spatial-reconstruction",))
    tex.write_text(
        "Full build & 8469 jobs, success \\\\ % @@JOBSAFTER@@\n",
        encoding="utf-8",
    )
    assert guard.placeholder_errors(tmp_path, ("papers/spatial-reconstruction",)) == []


def test_lean_artifact_without_toolchain_declaration_is_rejected(tmp_path: Path) -> None:
    write_root_pins(tmp_path)
    target = tmp_path / "papers" / "parity-barriers"
    target.mkdir(parents=True)
    (target / "ParityBarrier.lean").write_text("import Mathlib\n", encoding="utf-8")
    errors = guard.toolchain_errors(tmp_path, ("papers/parity-barriers",))
    assert errors == [
        "papers/parity-barriers: Lean artifact has no ARTIFACT-TOOLCHAIN.json"
    ]


def test_declared_source_hash_drift_is_rejected(tmp_path: Path) -> None:
    write_root_pins(tmp_path)
    target = tmp_path / "papers" / "parity-barriers"
    target.mkdir(parents=True)
    source = target / "ParityBarrier.lean"
    evidence = target / "LEAN-VERIFICATION-LOG.txt"
    source.write_text("import Mathlib\n", encoding="utf-8")
    evidence.write_text("recorded\n", encoding="utf-8")
    declaration = {
        "sources": [
            {
                "path": "papers/parity-barriers/ParityBarrier.lean",
                "sha256_lf": "0" * 64,
            }
        ],
        "verified_environment": {
            "lean_toolchain": "leanprover/lean4:v4.30.0-rc2",
            "mathlib_commit": "cd3b69baae9cd81a572a3720f2372655eca39038",
            "command": "lake env lean ParityBarrier.lean",
            "evidence_path": "papers/parity-barriers/LEAN-VERIFICATION-LOG.txt",
            "evidence_sha256_lf": guard.sha256_lf(evidence),
        },
        "main_tree_environment": {
            "lean_toolchain": "leanprover/lean4:v4.29.0-rc6",
            "mathlib_commit": "07642720480157414db592fa85b626dafb71355b",
        },
        "compatibility": {
            "status": "not_reproduced_on_main_tree",
            "statement_change_requirement": "not_determined",
            "migration_authorized": False,
        },
    }
    (target / "ARTIFACT-TOOLCHAIN.json").write_text(
        json.dumps(declaration), encoding="utf-8"
    )
    errors = guard.toolchain_errors(tmp_path, ("papers/parity-barriers",))
    assert any("declared source hash mismatch" in error for error in errors)
