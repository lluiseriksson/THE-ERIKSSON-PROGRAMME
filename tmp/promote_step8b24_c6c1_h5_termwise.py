#!/usr/bin/env python3
"""Fail-closed promotion of the H5a--H5c PRE-VALIDATION overlay."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h5-termwise-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H5-TERMWISE-OVERLAY-MANIFEST.json"
EXPECTED_MANIFEST_SHA256 = (
    "826C1D7567A949FE6E212CC61E053C3009C69AF94A394144158B269782C40640"
)
PREREQUISITES = (
    "BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope",
    "BalabanCMP89Eq249FineLatticeStabilizedFourierLeftDerivativeKernel",
    "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativePeriodization",
    "BalabanCMP116CMP89PhysicalBondDisplacementDictionary",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def git(*args: str) -> str:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if child.returncode != 0:
        raise SystemExit("GIT_FAIL " + " ".join(args) + "\n" + child.stderr)
    return child.stdout.strip()


def require_prerequisites() -> None:
    core = (ROOT / "YangMillsCore.lean").read_text(encoding="utf-8")
    for module in PREREQUISITES:
        for suffix in (".lean", "Audit.lean"):
            relative = Path("YangMills/RG") / f"{module}{suffix}"
            path = ROOT / relative
            if not path.is_file():
                raise SystemExit(f"H5_TERMWISE_PREREQUISITE_MISSING={relative.as_posix()}")
            if "PRE-VALIDATION:" in path.read_text(encoding="utf-8"):
                raise SystemExit(
                    f"H5_TERMWISE_PREREQUISITE_NOT_SEALED={relative.as_posix()}"
                )
        audit_import = f"import YangMills.RG.{module}Audit"
        if audit_import not in core:
            raise SystemExit(f"H5_TERMWISE_PREREQUISITE_NOT_IN_CORE={audit_import}")


def promotion_plan() -> list[tuple[Path, bytes]]:
    require_prerequisites()
    measured_manifest = sha256(MANIFEST.read_bytes())
    if measured_manifest != EXPECTED_MANIFEST_SHA256:
        raise SystemExit(f"H5_TERMWISE_MANIFEST_DRIFT={measured_manifest}")
    payload = json.loads(MANIFEST.read_text(encoding="utf-8"))
    records: list[dict[str, object]] = payload["files"]
    if (
        payload.get("status") != "PRE-VALIDATION"
        or payload.get("compiler_verified") is not False
        or payload.get("declarations") != 3
        or payload.get("axiom_prints") != 3
        or payload.get("positive_mass_premise") != "ABSENT"
        or payload.get("derivative_and_bond_directions") != "INDEPENDENT"
        or payload.get("tsum_transport") != "OPEN"
        or payload.get("owner_metric_dictionary") != "OPEN"
        or payload.get("window15") != "OPEN"
        or payload.get("terminal_fields") != "OPEN"
        or len(records) != 4
    ):
        raise SystemExit("H5_TERMWISE_MANIFEST_SEMANTIC_MISMATCH")

    result: list[tuple[Path, bytes]] = []
    for record in records:
        relative = Path(str(record["path"]))
        if relative.parent != Path("YangMills/RG"):
            raise SystemExit(f"H5_TERMWISE_BAD_TARGET={relative.as_posix()}")
        source = OVERLAY / relative
        target = ROOT / relative
        if not source.is_file():
            raise SystemExit(f"H5_TERMWISE_OVERLAY_FILE_MISSING={relative.as_posix()}")
        content = source.read_bytes()
        if sha256(content) != record["sha256"]:
            raise SystemExit(f"H5_TERMWISE_OVERLAY_BLOB_DRIFT={relative.as_posix()}")
        if len(content) != record["bytes"]:
            raise SystemExit(f"H5_TERMWISE_OVERLAY_SIZE_DRIFT={relative.as_posix()}")
        text = content.decode("utf-8")
        if text.count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"H5_TERMWISE_PRE_MARKER_COUNT={relative.as_posix()}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"H5_TERMWISE_FORBIDDEN_PLACEHOLDER={relative.as_posix()}")
        if target.exists():
            raise SystemExit(f"H5_TERMWISE_TARGET_ALREADY_EXISTS={relative.as_posix()}")
        result.append((target, content))
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    actual = git("rev-parse", "HEAD")
    if actual != args.expected_head:
        raise SystemExit(f"HEAD_MISMATCH={actual}")
    if subprocess.run(
        ["git", "-c", "safe.directory=*", "diff", "--quiet"], cwd=ROOT
    ).returncode != 0:
        raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
    if subprocess.run(
        ["git", "-c", "safe.directory=*", "diff", "--cached", "--quiet"], cwd=ROOT
    ).returncode != 0:
        raise SystemExit("INDEX_NOT_CLEAN")

    promotion = promotion_plan()
    if not args.write:
        print(
            "STEP8B24_C6C1_H5_TERMWISE_PROMOTION_DRY_RUN_OK "
            f"head={actual} new_files={len(promotion)} "
            f"manifest={EXPECTED_MANIFEST_SHA256}"
        )
        return 0

    for target, content in promotion:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    for target, content in promotion:
        if target.read_bytes() != content:
            raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={target.relative_to(ROOT)}")
    print(
        "STEP8B24_C6C1_H5_TERMWISE_PROMOTION_WRITE_OK "
        f"base_head={actual} new_files={len(promotion)} "
        f"manifest={EXPECTED_MANIFEST_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
