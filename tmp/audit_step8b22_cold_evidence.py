#!/usr/bin/env python3
"""Read-only validator for the Step 8b.22 cold GitHub artifact.

The GitHub artifact ZIP must be preserved separately from its extracted
contents so the transport object and the deterministic inner archive both
receive explicit digests.  This script never infers PASS from a run summary.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import tarfile
import zipfile
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath


SOURCE_SHA = "534493728038813f3772f8b3b073237f4da1884e"
WORKFLOW_SHA = "b05ef65af97a95752d1c929e30749d886d425d8d"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
TOOLCHAIN_ASSET_SHA256 = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)
INNER_ARCHIVE = "cmp99-finite-grid-aliasing-evidence.tar.gz"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STAGES = ("cmp99_finite_grid_aliasing_focal", "cmp99_finite_grid_aliasing_audit")


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


def parse_stage_times(path: Path) -> dict[str, dict[str, object]]:
    starts: dict[str, datetime] = {}
    result: dict[str, dict[str, object]] = {}
    start_re = re.compile(r"^STAGE=(\S+) STARTED=(\S+) CMD=(.*)$")
    end_re = re.compile(r"^STAGE=(\S+) EXIT=(\d+) ENDED=(\S+)$")
    for line in path.read_text(encoding="utf-8").splitlines():
        if match := start_re.match(line):
            stage, stamp, command = match.groups()
            starts[stage] = datetime.fromisoformat(stamp.replace("Z", "+00:00"))
            result[stage] = {"command": command}
        elif match := end_re.match(line):
            stage, code, stamp = match.groups()
            require(stage in starts, f"stage end without start: {stage}")
            ended = datetime.fromisoformat(stamp.replace("Z", "+00:00"))
            result[stage].update(
                exit=int(code),
                started=starts[stage].astimezone(timezone.utc).isoformat(),
                ended=ended.astimezone(timezone.utc).isoformat(),
                seconds=int((ended - starts[stage]).total_seconds()),
            )
    require(set(result) == set(STAGES), f"stage set {sorted(result)}")
    for stage in STAGES:
        require(result[stage].get("exit") == 0, f"nonzero or missing exit: {stage}")
    return result


def parse_axioms(text: str) -> list[list[str]]:
    compact = re.sub(r"\s+", "", text)
    for forbidden in ("sorryAx", "ofReduceBool"):
        require(forbidden not in compact, f"forbidden axiom: {forbidden}")
    bodies = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    require(len(bodies) == 7, f"axiom block count {len(bodies)}, expected 7")
    parsed: list[list[str]] = []
    for body in bodies:
        names = {item for item in body.split(",") if item}
        require(names.issubset(ALLOWED_AXIOMS), f"unexpected axiom set: {sorted(names)}")
        parsed.append(sorted(names))
    return parsed


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
    evidence = root / "evidence"
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
    require(checkpoint.get("ACTUAL_HEAD") == SOURCE_SHA, "wrong ACTUAL_HEAD")
    require(checkpoint.get("WORKFLOW_SHA") == WORKFLOW_SHA, "wrong WORKFLOW_SHA")
    require(checkpoint.get("COLD_MODE") == "true", "COLD_MODE is not true")

    toolchain = (evidence / "toolchain.txt").read_text(encoding="utf-8")
    require(f"TOOLCHAIN_URL={TOOLCHAIN_URL}" in toolchain, "wrong toolchain URL")
    require(
        f"TOOLCHAIN_ASSET_SHA256={TOOLCHAIN_ASSET_SHA256}" in toolchain,
        "wrong toolchain asset digest",
    )
    require(re.search(r"^[0-9a-f]{64}  .*/lean$", toolchain, re.MULTILINE) is not None,
            "missing Lean executable digest")
    require(re.search(r"^[0-9a-f]{64}  .*/lake$", toolchain, re.MULTILINE) is not None,
            "missing Lake executable digest")
    require("Lean (version 4.29.0-rc6" in toolchain, "wrong Lean version")
    require("Lake version " in toolchain, "missing Lake version")

    require(
        (evidence / "mathlib.txt").read_text(encoding="utf-8").strip()
        == f"MATHLIB_SHA={MATHLIB_SHA}",
        "wrong Mathlib pin",
    )
    require(
        "LEAN_OVERLAY_TEXT_OK files=2" in
        (evidence / "text-guard.log").read_text(encoding="utf-8"),
        "text guard did not pass exact pair",
    )
    require(
        "LEAN_IMPORT_PREFIX_OK" in
        (evidence / "import-prefix-guard.log").read_text(encoding="utf-8"),
        "import-prefix guard did not pass",
    )

    stages = parse_stage_times(evidence / "stages.txt")
    focal = (evidence / f"{STAGES[0]}.log").read_text(encoding="utf-8")
    focal_lines = [line.strip() for line in focal.splitlines() if line.strip()]
    build_lines = [
        line for line in focal_lines
        if re.fullmatch(r"Build completed successfully \(\d+ jobs\)\.", line)
    ]
    require(len(build_lines) == 1, f"literal build-line count {len(build_lines)}, expected 1")
    require(focal_lines[-1] == build_lines[0], "literal build line is not final focal line")
    require(
        "warning: YangMills/RG/BalabanCMP99FlatFiniteGridAliasing.lean:" not in focal,
        "new-module linter warning present",
    )
    jobs = int(re.search(r"\((\d+) jobs\)", build_lines[0]).group(1))

    audit_text = (evidence / f"{STAGES[1]}.log").read_text(encoding="utf-8")
    axioms = parse_axioms(audit_text)
    recorded_axioms = json.loads((evidence / "axioms.json").read_text(encoding="utf-8"))
    require(recorded_axioms == axioms, "axioms.json differs from measured audit log")
    require(
        (evidence / "FINAL_STATUS").read_text(encoding="utf-8") == "FINAL_STATUS=PASS\n",
        "FINAL_STATUS is not literal PASS",
    )

    manifest_count = verify_sha256sums(root, evidence / "SHA256SUMS")
    evidence_manifest_sha256 = digest(evidence / "SHA256SUMS").upper()
    archive_line = (evidence / "ARCHIVE_SHA256").read_text(encoding="utf-8").strip()
    archive_match = re.fullmatch(rf"([0-9a-f]{{64}})  {re.escape(INNER_ARCHIVE)}", archive_line)
    require(archive_match is not None, "malformed ARCHIVE_SHA256")
    inner_sha256 = digest(inner)
    require(inner_sha256 == archive_match.group(1), "inner archive digest mismatch")
    inner_members = verify_inner_archive(root, inner)
    outer_members = verify_outer_zip(root, outer_zip)
    outer_sha256 = digest(outer_zip)

    return {
        "source_sha": SOURCE_SHA,
        "workflow_sha": WORKFLOW_SHA,
        "focal_jobs": jobs,
        "stages": stages,
        "axioms": axioms,
        "manifest_entries": manifest_count,
        "evidence_manifest_sha256": evidence_manifest_sha256,
        "inner_members": inner_members,
        "outer_members": outer_members,
        "inner_archive_sha256": inner_sha256.upper(),
        "outer_artifact_zip_sha256": outer_sha256.upper(),
    }


def print_result(result: dict[str, object]) -> None:
    print("STEP8B22_COLD_EVIDENCE_OK")
    print(f"source_sha={result['source_sha']}")
    print(f"workflow_sha={result['workflow_sha']}")
    print(f"focal_jobs={result['focal_jobs']}")
    stages = result["stages"]
    assert isinstance(stages, dict)
    for stage in STAGES:
        print(
            f"stage={stage} exit={stages[stage]['exit']} "
            f"seconds={stages[stage]['seconds']}"
        )
    axioms = result["axioms"]
    assert isinstance(axioms, list)
    for index, names in enumerate(axioms, start=1):
        print(f"axiom_block_{index}={','.join(names)}")
    print(f"manifest_entries={result['manifest_entries']}")
    print(f"evidence_manifest_sha256={result['evidence_manifest_sha256']}")
    print(f"inner_members={result['inner_members']}")
    print(f"outer_members={result['outer_members']}")
    print(f"inner_archive_sha256={result['inner_archive_sha256']}")
    print(f"outer_artifact_zip_sha256={result['outer_artifact_zip_sha256']}")


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
    except (
        OSError,
        ValueError,
        tarfile.TarError,
        zipfile.BadZipFile,
        json.JSONDecodeError,
    ) as error:
        print(f"STEP8B22_COLD_EVIDENCE_FAIL: {error}")
        raise SystemExit(1)
