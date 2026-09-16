#!/usr/bin/env python3
"""Fail-closed promotion of the H5d0a--H5d0b PRE-VALIDATION overlay."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h5-holder-factor-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H5-HOLDER-FACTOR-OVERLAY-MANIFEST.json"
EXPECTED_MANIFEST_SHA256 = (
    "E5FCFA044FECE89BC64229D1D55DB5C2E4F2C68D752F0F38EAED4A6AFD69D2C3"
)
PREREQUISITES = (
    "BalabanCMP89Eq249PhysicalFineHolderPhaseQuotient",
    "BalabanCMP89Eq249StabilizedComplexIntegrand",
    "BalabanCMP89Eq249MassUniformRealSliceRecombination",
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
                raise SystemExit(f"H5_HOLDER_FACTOR_PREREQUISITE_MISSING={relative.as_posix()}")
            if "PRE-VALIDATION:" in path.read_text(encoding="utf-8"):
                raise SystemExit(
                    f"H5_HOLDER_FACTOR_PREREQUISITE_NOT_SEALED={relative.as_posix()}"
                )
        audit_import = f"import YangMills.RG.{module}Audit"
        if audit_import not in core:
            raise SystemExit(f"H5_HOLDER_FACTOR_PREREQUISITE_NOT_IN_CORE={audit_import}")


def promotion_plan() -> list[tuple[Path, bytes]]:
    require_prerequisites()
    measured_manifest = sha256(MANIFEST.read_bytes())
    if measured_manifest != EXPECTED_MANIFEST_SHA256:
        raise SystemExit(f"H5_HOLDER_FACTOR_MANIFEST_DRIFT={measured_manifest}")
    payload = json.loads(MANIFEST.read_text(encoding="utf-8"))
    records: list[dict[str, object]] = payload["files"]
    if (
        payload.get("status") != "PRE-VALIDATION"
        or payload.get("compiler_verified") is not False
        or payload.get("declarations") != 7
        or payload.get("axiom_prints") != 7
        or payload.get("general_alpha_literal") is not True
        or payload.get("alpha_zero_identity") is not True
        or payload.get("xi_rpow_inverse_extracted_before_norm") is not True
        or payload.get("positive_mass_premise") != "ABSENT"
        or payload.get("generated_operator") != "OPEN"
        or payload.get("tsum_transport") != "OPEN"
        or payload.get("owner_metric_dictionary") != "OPEN"
        or payload.get("window15") != "OPEN"
        or payload.get("terminal_fields") != "OPEN"
        or len(records) != 4
    ):
        raise SystemExit("H5_HOLDER_FACTOR_MANIFEST_SEMANTIC_MISMATCH")

    result: list[tuple[Path, bytes]] = []
    for record in records:
        relative = Path(str(record["path"]))
        if relative.parent != Path("YangMills/RG"):
            raise SystemExit(f"H5_HOLDER_FACTOR_BAD_TARGET={relative.as_posix()}")
        source = OVERLAY / relative
        target = ROOT / relative
        if not source.is_file():
            raise SystemExit(f"H5_HOLDER_FACTOR_OVERLAY_FILE_MISSING={relative.as_posix()}")
        content = source.read_bytes()
        if sha256(content) != record["sha256"]:
            raise SystemExit(f"H5_HOLDER_FACTOR_OVERLAY_BLOB_DRIFT={relative.as_posix()}")
        if len(content) != record["bytes"]:
            raise SystemExit(f"H5_HOLDER_FACTOR_OVERLAY_SIZE_DRIFT={relative.as_posix()}")
        text = content.decode("utf-8")
        if text.count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"H5_HOLDER_FACTOR_PRE_MARKER_COUNT={relative.as_posix()}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"H5_HOLDER_FACTOR_FORBIDDEN_PLACEHOLDER={relative.as_posix()}")
        if target.exists():
            raise SystemExit(f"H5_HOLDER_FACTOR_TARGET_ALREADY_EXISTS={relative.as_posix()}")
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
            "STEP8B24_C6C1_H5_HOLDER_FACTOR_PROMOTION_DRY_RUN_OK "
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
        "STEP8B24_C6C1_H5_HOLDER_FACTOR_PROMOTION_WRITE_OK "
        f"base_head={actual} new_files={len(promotion)} "
        f"manifest={EXPECTED_MANIFEST_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
