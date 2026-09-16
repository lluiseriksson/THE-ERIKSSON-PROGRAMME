#!/usr/bin/env python3
"""Fail-closed validator for the terminal uniform/localized B0 artifact."""

from __future__ import annotations

import argparse
import hashlib
import re
import tarfile
import zipfile
from pathlib import Path, PurePosixPath


SOURCE_SHA = "73bb1a2008c557840a91e50d8abe6b874947f7ee"
CONTROL_SHA = "ebccd7e8811d639587563fe060705811163e1c57"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
TOOLCHAIN_ASSET_SHA256 = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)
INNER_ARCHIVE = "source-flow-uniform-localized-b0-evidence.tar.gz"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STATUS_FILES = {
    "focal.status": "source_flow_uniform_point_source_b0_focal",
    "uniform-audit.status": "source_flow_uniform_point_source_b0_audit",
    "localized-focal.status": "source_flow_localized_field_b0_focal",
    "localized-audit.status": "source_flow_localized_field_b0_audit",
}


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def key_values(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        if "=" in raw:
            key, value = raw.split("=", 1)
            result[key] = value
    return result


def parse_status(path: Path, expected_stage: str) -> int:
    text = path.read_text(encoding="utf-8").strip()
    match = re.fullmatch(r"stage=(\S+) exit=(\d+) seconds=(\d+)", text)
    require(match is not None, f"malformed status: {path.name}")
    stage, exit_code, seconds = match.groups()
    require(stage == expected_stage, f"wrong stage in {path.name}: {stage}")
    require(exit_code == "0", f"nonzero exit in {path.name}: {exit_code}")
    return int(seconds)


def parse_axioms(text: str, expected: int, label: str) -> list[list[str]]:
    compact = re.sub(r"\s+", "", text)
    for forbidden in ("sorryAx", "ofReduceBool"):
        require(forbidden not in compact, f"{label}: forbidden axiom {forbidden}")
    bodies = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    require(len(bodies) == expected, f"{label}: axiom block count {len(bodies)}, expected {expected}")
    parsed: list[list[str]] = []
    for body in bodies:
        names = {item for item in body.split(",") if item}
        require(names.issubset(ALLOWED_AXIOMS), f"{label}: unexpected axioms {sorted(names)}")
        parsed.append(sorted(names))
    return parsed


def parse_recorded_axioms(path: Path, prefix: str, expected: int) -> list[list[str]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    require(len(lines) == expected, f"{path.name}: line count {len(lines)}, expected {expected}")
    result: list[list[str]] = []
    for index, line in enumerate(lines, start=1):
        key = f"{prefix}_axiom_block_{index}="
        require(line.startswith(key), f"{path.name}: wrong key at line {index}")
        names = sorted(item for item in line[len(key):].split(",") if item)
        require(set(names).issubset(ALLOWED_AXIOMS), f"{path.name}: unexpected axioms")
        result.append(names)
    return result


def verify_sha256sums(root: Path, sums_path: Path) -> int:
    count = 0
    for raw in sums_path.read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", raw)
        require(match is not None, f"malformed SHA256SUMS line: {raw!r}")
        expected, relative = match.groups()
        target = root / PurePosixPath(relative)
        require(target.is_file(), f"manifest target missing: {relative}")
        require(digest(target) == expected, f"manifest digest mismatch: {relative}")
        count += 1
    require(count > 0, "empty SHA256SUMS")
    return count


def verify_inner_archive(root: Path, archive: Path) -> int:
    count = 0
    with tarfile.open(archive, "r:gz") as packed:
        members = [member for member in packed.getmembers() if member.isfile()]
        names = [member.name.removeprefix("./") for member in members]
        require(len(names) == len(set(names)), "duplicate inner archive member")
        require("evidence/ARCHIVE_SHA256" not in names, "self-hash unexpectedly archived")
        for member, name in zip(members, names, strict=True):
            require(name.startswith("evidence/"), f"unexpected inner member: {name}")
            sibling = root / PurePosixPath(name)
            require(sibling.is_file(), f"inner member lacks extracted sibling: {name}")
            stream = packed.extractfile(member)
            require(stream is not None, f"cannot read inner member: {name}")
            require(stream.read() == sibling.read_bytes(), f"inner/sibling mismatch: {name}")
            count += 1
    require(count > 0, "empty inner archive")
    return count


def verify_outer_zip(root: Path, archive: Path) -> int:
    extracted = {
        path.relative_to(root).as_posix(): path
        for path in root.rglob("*")
        if path.is_file()
    }
    with zipfile.ZipFile(archive) as packed:
        infos = [info for info in packed.infolist() if not info.is_dir()]
        names = [PurePosixPath(info.filename).as_posix().removeprefix("./") for info in infos]
        require(len(names) == len(set(names)), "duplicate outer ZIP member")
        for name in names:
            parts = PurePosixPath(name).parts
            require(".." not in parts and not name.startswith("/"), f"unsafe ZIP member: {name}")
        require(set(names) == set(extracted), "outer ZIP/extracted member-set mismatch")
        for info, name in zip(infos, names, strict=True):
            require(packed.read(info) == extracted[name].read_bytes(), f"ZIP/extracted mismatch: {name}")
    require(len(infos) > 0, "empty outer ZIP")
    return len(infos)


def build_jobs(path: Path, label: str) -> int:
    text = path.read_text(encoding="utf-8")
    matches = re.findall(r"Build completed successfully \((\d+) jobs\)\.", text)
    require(len(matches) == 1, f"{label}: successful build-line count {len(matches)}, expected 1")
    return int(matches[0])


def validate(artifact_root: Path, outer_zip: Path) -> dict[str, object]:
    root = artifact_root.resolve()
    outer_zip = outer_zip.resolve()
    evidence = root / "evidence"
    inner = root / INNER_ARCHIVE
    require(evidence.is_dir(), f"missing evidence directory: {evidence}")
    require(outer_zip.is_file(), f"missing raw artifact ZIP: {outer_zip}")
    require(inner.is_file(), f"missing inner archive: {inner}")

    checkpoint = key_values(evidence / "checkpoint.txt")
    require(checkpoint.get("SOURCE_SHA") == SOURCE_SHA, "wrong SOURCE_SHA")
    require(checkpoint.get("ACTUAL_SOURCE_HEAD") == SOURCE_SHA, "wrong ACTUAL_SOURCE_HEAD")
    require(checkpoint.get("CONTROL_SHA") == CONTROL_SHA, "wrong CONTROL_SHA")
    require(checkpoint.get("GITHUB_SHA") == CONTROL_SHA, "wrong GITHUB_SHA")
    require(checkpoint.get("COLD_MODE") == "true", "COLD_MODE is not true")

    toolchain = (evidence / "toolchain.txt").read_text(encoding="utf-8")
    require(f"TOOLCHAIN_URL={TOOLCHAIN_URL}" in toolchain, "wrong toolchain URL")
    require(f"TOOLCHAIN_ASSET_SHA256={TOOLCHAIN_ASSET_SHA256}" in toolchain, "wrong toolchain digest")
    require(re.search(r"^[0-9a-f]{64}  .*/lean$", toolchain, re.MULTILINE) is not None,
            "missing Lean executable digest")
    require(re.search(r"^[0-9a-f]{64}  .*/lake$", toolchain, re.MULTILINE) is not None,
            "missing Lake executable digest")
    require("Lean (version 4.29.0-rc6" in toolchain, "wrong Lean version")
    require("Lake version " in toolchain, "missing Lake version")
    require((evidence / "mathlib.txt").read_text(encoding="utf-8").strip()
            == f"MATHLIB_SHA={MATHLIB_SHA}", "wrong Mathlib pin")

    seconds = {
        stage: parse_status(evidence / filename, stage)
        for filename, stage in STATUS_FILES.items()
    }
    jobs = {
        "uniform": build_jobs(evidence / "focal.log", "uniform focal"),
        "localized": build_jobs(evidence / "localized-focal.log", "localized focal"),
    }

    uniform = parse_axioms((evidence / "uniform-audit.log").read_text(encoding="utf-8"), 5, "uniform")
    localized = parse_axioms((evidence / "localized-audit.log").read_text(encoding="utf-8"), 2, "localized")
    require(parse_recorded_axioms(evidence / "uniform-axioms.txt", "uniform", 5) == uniform,
            "uniform recorded axioms differ from audit log")
    require(parse_recorded_axioms(evidence / "localized-axioms.txt", "localized", 2) == localized,
            "localized recorded axioms differ from audit log")
    require((evidence / "FINAL_STATUS").read_text(encoding="utf-8") == "FINAL_STATUS=PASS\n",
            "FINAL_STATUS is not literal PASS")

    manifest_count = verify_sha256sums(root, evidence / "SHA256SUMS")
    archive_line = (evidence / "ARCHIVE_SHA256").read_text(encoding="utf-8").strip()
    match = re.fullmatch(rf"([0-9a-f]{{64}})  {re.escape(INNER_ARCHIVE)}", archive_line)
    require(match is not None, "malformed ARCHIVE_SHA256")
    inner_sha = digest(inner)
    require(inner_sha == match.group(1), "inner archive digest mismatch")
    inner_members = verify_inner_archive(root, inner)
    outer_members = verify_outer_zip(root, outer_zip)

    return {
        "source_sha": SOURCE_SHA,
        "control_sha": CONTROL_SHA,
        "jobs": jobs,
        "seconds": seconds,
        "uniform_axioms": uniform,
        "localized_axioms": localized,
        "manifest_entries": manifest_count,
        "manifest_sha256": digest(evidence / "SHA256SUMS").upper(),
        "inner_members": inner_members,
        "outer_members": outer_members,
        "inner_sha256": inner_sha.upper(),
        "outer_sha256": digest(outer_zip).upper(),
    }


def print_result(result: dict[str, object]) -> None:
    print("UNIFORM_LOCALIZED_B0_TERMINAL_EVIDENCE_OK")
    print(f"source_sha={result['source_sha']}")
    print(f"control_sha={result['control_sha']}")
    jobs = result["jobs"]
    seconds = result["seconds"]
    assert isinstance(jobs, dict) and isinstance(seconds, dict)
    print(f"uniform_focal_jobs={jobs['uniform']}")
    print(f"localized_focal_jobs={jobs['localized']}")
    for stage, elapsed in seconds.items():
        print(f"stage={stage} exit=0 seconds={elapsed}")
    for label in ("uniform", "localized"):
        blocks = result[f"{label}_axioms"]
        assert isinstance(blocks, list)
        for index, names in enumerate(blocks, start=1):
            print(f"{label}_axiom_block_{index}={','.join(names)}")
    print(f"manifest_entries={result['manifest_entries']}")
    print(f"evidence_manifest_sha256={result['manifest_sha256']}")
    print(f"inner_members={result['inner_members']}")
    print(f"outer_members={result['outer_members']}")
    print(f"inner_archive_sha256={result['inner_sha256']}")
    print(f"outer_artifact_zip_sha256={result['outer_sha256']}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact-root", required=True, type=Path)
    parser.add_argument("--outer-zip", required=True, type=Path)
    args = parser.parse_args()
    print_result(validate(args.artifact_root, args.outer_zip))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, tarfile.TarError, zipfile.BadZipFile) as error:
        print(f"UNIFORM_LOCALIZED_B0_TERMINAL_EVIDENCE_FAIL: {error}")
        raise SystemExit(1)
