#!/usr/bin/env python3
"""Adversarial checks for PR 37's publication-register validator.

The producer validator is loaded from an exact clean checkout, then pointed at
an isolated temporary copy.  The copy contains only the files and empty
artifact sentinels needed by the validator.  Two mutations test whether the
validator actually defends completeness and title fidelity.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import shutil
import tempfile
from pathlib import Path, PurePosixPath


def copy_validator_fixture(module: object, root: Path) -> None:
    producer_root = Path(module.ROOT)
    relative_files = {
        "docs/publications.json",
        "docs/PUBLICATIONS.md",
        *module.ACTIVE_FRONT_DOORS,
    }
    data = json.loads((producer_root / "docs/publications.json").read_text("utf-8"))
    artifact_files = {
        entry["artifact"]
        for entry in data["entries"]
        if isinstance(entry.get("artifact"), str)
    }

    for relative in sorted(relative_files):
        source = producer_root.joinpath(*PurePosixPath(relative).parts)
        target = root.joinpath(*PurePosixPath(relative).parts)
        target.parent.mkdir(parents=True, exist_ok=True)
        if source.is_file():
            shutil.copyfile(source, target)
        else:
            raise FileNotFoundError(f"fixture source is missing: {source}")

    # The producer validator checks only that artifact paths are files.  Empty
    # sentinels avoid copying large PDFs while preserving that exact behavior.
    for relative in sorted(artifact_files):
        source = producer_root.joinpath(*PurePosixPath(relative).parts)
        if not source.is_file():
            raise FileNotFoundError(f"fixture source is missing: {source}")
        target = root.joinpath(*PurePosixPath(relative).parts)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.touch()


def point_module_at(module: object, root: Path) -> None:
    module.ROOT = root
    module.DATA_PATH = root / "docs" / "publications.json"
    module.REGISTER_PATH = root / "docs" / "PUBLICATIONS.md"


def run_mutation(module: object, root: Path, mutate: object) -> list[str]:
    data_path = root / "docs" / "publications.json"
    original = data_path.read_text("utf-8")
    data = json.loads(original)
    mutate(data)
    data_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    try:
        return module.validate_publications()
    finally:
        data_path.write_text(original, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "checkout",
        type=Path,
        help="clean PR 37 checkout containing scripts/validate_publications.py",
    )
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    validator = checkout / "scripts" / "validate_publications.py"

    spec = importlib.util.spec_from_file_location("producer_publications", validator)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {validator}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    with tempfile.TemporaryDirectory(prefix="pr37-publications-audit-") as tmp:
        root = Path(tmp)
        copy_validator_fixture(module, root)
        point_module_at(module, root)

        baseline = module.validate_publications()
        print(f"baseline_errors={len(baseline)}")
        if baseline:
            for error in baseline:
                print(f"  {error}")
            return 2

        def delete_0093(data: dict[str, object]) -> None:
            data["entries"] = [
                entry
                for entry in data["entries"]
                if entry.get("id") != "2607.0093"
            ]

        missing_entry = run_mutation(module, root, delete_0093)
        print(f"delete_2607.0093_errors={len(missing_entry)}")

        def falsify_surface_title(data: dict[str, object]) -> None:
            for entry in data["entries"]:
                if entry.get("id") == "2607.0089":
                    entry["title"] = "WRONG TITLE ACCEPTED BY INTERNAL VALIDATOR"

        wrong_title = run_mutation(module, root, falsify_surface_title)
        print(f"wrong_2607.0089_title_errors={len(wrong_title)}")

        accepted = not missing_entry and not wrong_title
        print(
            "ADVERSARIAL_WITNESS="
            + ("VALIDATOR_ACCEPTS_BOTH_MUTATIONS" if accepted else "NOT_REPRODUCED")
        )
        return 0 if accepted else 1


if __name__ == "__main__":
    raise SystemExit(main())
