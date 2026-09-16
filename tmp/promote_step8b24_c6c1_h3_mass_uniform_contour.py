#!/usr/bin/env python3
"""Fail-closed promotion of the H3a/H3b mass-uniform contour overlay."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess

import prepare_step8b24_c6c1_h5_holder_factor_overlay as shared


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h3-mass-uniform-contour-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H3-MASS-UNIFORM-CONTOUR-OVERLAY-MANIFEST.json"
EXPECTED_MANIFEST_SHA256 = (
    "D887872AF1D88F8139A590FF07AC1F35F4D787C2BF984D0DDB9767F26830BC89"
)
PREREQUISITES = (
    "BalabanCMP89Eq248GreenMassUniformHolomorphy",
    "BalabanCMP89Eq251StabilizedIntegrandHolomorphy",
    "BalabanCMP89Eq251DisplayedIntegrandPeriodicity",
    "BalabanCMP89Eq251OneCoordinateContourShift",
)
SEALED_TRANSITIVE_PREREQUISITES = (
    "BalabanCMP89Eq251FineLatticeDisplayedEndpointPeriodicity",
)


def git(*args: str) -> str:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        encoding="utf-8", check=False,
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
                raise SystemExit(f"H3_MASS_UNIFORM_PREREQUISITE_MISSING={relative.as_posix()}")
            if "PRE-VALIDATION:" in path.read_text(encoding="utf-8"):
                raise SystemExit(f"H3_MASS_UNIFORM_PREREQUISITE_NOT_SEALED={relative.as_posix()}")
        audit_import = f"import YangMills.RG.{module}Audit"
        if audit_import not in core:
            raise SystemExit(f"H3_MASS_UNIFORM_PREREQUISITE_NOT_IN_CORE={audit_import}")
    for module in SEALED_TRANSITIVE_PREREQUISITES:
        for suffix in (".lean", "Audit.lean"):
            relative = Path("YangMills/RG") / f"{module}{suffix}"
            path = ROOT / relative
            if not path.is_file():
                raise SystemExit(
                    f"H3_MASS_UNIFORM_TRANSITIVE_PREREQUISITE_MISSING={relative.as_posix()}"
                )
            if "PRE-VALIDATION:" in path.read_text(encoding="utf-8"):
                raise SystemExit(
                    f"H3_MASS_UNIFORM_TRANSITIVE_PREREQUISITE_NOT_SEALED={relative.as_posix()}"
                )


def promotion_plan() -> list[tuple[Path, bytes]]:
    require_prerequisites()
    measured = shared.sha256(MANIFEST.read_bytes())
    if measured != EXPECTED_MANIFEST_SHA256:
        raise SystemExit(f"H3_MASS_UNIFORM_MANIFEST_DRIFT={measured}")
    payload = json.loads(MANIFEST.read_text(encoding="utf-8"))
    records: list[dict[str, object]] = payload["files"]
    if (
        payload.get("status") != "PRE-VALIDATION"
        or payload.get("compiler_verified") is not False
        or payload.get("declarations") != 10
        or payload.get("axiom_prints") != 10
        or payload.get("positive_mass_premise") != "ABSENT"
        or payload.get("polydisc_gate") != "ALL_COORDINATES"
        or payload.get("fine_lattice_displacements") != "BOTH_LITERAL"
        or payload.get("product_telescope") != "OPEN"
        or payload.get("integral_bound") != "OPEN"
        or payload.get("owner_dictionary") != "OPEN"
        or payload.get("regional_B0") != "OPEN"
        or payload.get("window15") != "OPEN"
        or payload.get("terminal_fields") != "OPEN"
        or len(records) != 6
    ):
        raise SystemExit("H3_MASS_UNIFORM_MANIFEST_SEMANTIC_MISMATCH")
    result: list[tuple[Path, bytes]] = []
    for record in records:
        relative = Path(str(record["path"]))
        if relative.parent != Path("YangMills/RG"):
            raise SystemExit(f"H3_MASS_UNIFORM_BAD_TARGET={relative.as_posix()}")
        source = OVERLAY / relative
        target = ROOT / relative
        if not source.is_file():
            raise SystemExit(f"H3_MASS_UNIFORM_OVERLAY_FILE_MISSING={relative.as_posix()}")
        content = source.read_bytes()
        if shared.sha256(content) != record["sha256"]:
            raise SystemExit(f"H3_MASS_UNIFORM_OVERLAY_BLOB_DRIFT={relative.as_posix()}")
        if len(content) != record["bytes"]:
            raise SystemExit(f"H3_MASS_UNIFORM_OVERLAY_SIZE_DRIFT={relative.as_posix()}")
        text = content.decode("utf-8")
        if text.count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"H3_MASS_UNIFORM_PRE_MARKER_COUNT={relative.as_posix()}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"H3_MASS_UNIFORM_FORBIDDEN_PLACEHOLDER={relative.as_posix()}")
        if target.exists():
            raise SystemExit(f"H3_MASS_UNIFORM_TARGET_ALREADY_EXISTS={relative.as_posix()}")
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
    if subprocess.run(["git", "-c", "safe.directory=*", "diff", "--quiet"], cwd=ROOT).returncode:
        raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
    if subprocess.run(["git", "-c", "safe.directory=*", "diff", "--cached", "--quiet"], cwd=ROOT).returncode:
        raise SystemExit("INDEX_NOT_CLEAN")
    promotion = promotion_plan()
    if not args.write:
        print(
            "STEP8B24_C6C1_H3_MASS_UNIFORM_PROMOTION_DRY_RUN_OK "
            f"head={actual} new_files={len(promotion)} manifest={EXPECTED_MANIFEST_SHA256}"
        )
        return 0
    for target, content in promotion:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    for target, content in promotion:
        if target.read_bytes() != content:
            raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={target.relative_to(ROOT)}")
    print(
        "STEP8B24_C6C1_H3_MASS_UNIFORM_PROMOTION_WRITE_OK "
        f"base_head={actual} new_files={len(promotion)} manifest={EXPECTED_MANIFEST_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
