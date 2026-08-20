#!/usr/bin/env python3
"""Fail-closed validator for the Step 8b.23 Units A--E cold artifact."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile
import zipfile
import runpy


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = runpy.run_path(str(ROOT / "tmp" / "generate_step8b23_ae_validation_runner.py"))
BRICKS: tuple[tuple[str, int], ...] = GENERATOR["BRICKS"]
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
TOOLCHAIN_ASSET_SHA256 = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
INNER_ARCHIVE = "step8b23-ae-evidence.tar.gz"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_FILES = 36
EXPECTED_BRICKS = 18
EXPECTED_AXIOMS = 124


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def git_blob(source_sha: str, path: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "cat-file", "blob", f"{source_sha}:{path}"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    require(
        child.returncode == 0,
        f"git blob unavailable: {path}: {child.stderr.decode(errors='replace')}",
    )
    return child.stdout


def expected_manifest(source_sha: str) -> list[tuple[str, str]]:
    paths: list[str] = GENERATOR["source_paths"]()
    result = [(hashlib.sha256(git_blob(source_sha, path)).hexdigest(), path) for path in paths]
    require(
        len(result) == EXPECTED_FILES,
        f"expected source scope {len(result)}, wanted {EXPECTED_FILES}",
    )
    return result


def stage_rows() -> list[tuple[str, str, str, int]]:
    result: list[tuple[str, str, str, int]] = []
    for index, (module, count) in enumerate(BRICKS, start=1):
        slug = module.removeprefix("Balaban").lower()
        result.append(
            (
                f"{index:02d}_{slug}_focal",
                f"{index:02d}_{slug}_audit",
                f"YangMills/RG/{module}.lean",
                count,
            )
        )
    require(len(result) == EXPECTED_BRICKS,
            f"stage-row count is not {EXPECTED_BRICKS}")
    require(sum(row[3] for row in result) == EXPECTED_AXIOMS,
            f"axiom total is not {EXPECTED_AXIOMS}")
    return result


def key_values(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        if "=" in raw:
            key, value = raw.split("=", 1)
            result[key] = value
    return result


def parse_stage_times(path: Path, expected: list[str]) -> dict[str, dict[str, object]]:
    starts: dict[str, datetime] = {}
    result: dict[str, dict[str, object]] = {}
    start_re = re.compile(r"^STAGE=(\S+) STARTED=(\S+) CMD=(.*)$")
    end_re = re.compile(r"^STAGE=(\S+) EXIT=(\d+) ENDED=(\S+)$")
    for line in path.read_text(encoding="utf-8").splitlines():
        if match := start_re.match(line):
            stage, stamp, command = match.groups()
            require(stage not in starts, f"duplicate stage start: {stage}")
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
    require(list(result) == expected, "stage order/set mismatch")
    for stage in expected:
        require(result[stage].get("exit") == 0, f"nonzero or missing exit: {stage}")
    return result


def parse_axioms(text: str, expected: int, stage: str) -> list[list[str]]:
    compact = re.sub(r"\s+", "", text)
    for forbidden in ("sorryAx", "ofReduceBool"):
        require(forbidden not in compact, f"forbidden axiom {forbidden}: {stage}")
    bodies = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    headers = len(bodies) + pure
    require(
        headers == expected,
        f"axiom header count {headers}/{expected} "
        f"(nonempty={len(bodies)}, empty={pure}): {stage}",
    )
    parsed: list[list[str]] = []
    for body in bodies:
        names = {item for item in body.split(",") if item}
        require(names.issubset(ALLOWED_AXIOMS), f"unexpected axioms {sorted(names)}: {stage}")
        parsed.append(sorted(names))
    parsed.extend([[] for _ in range(pure)])
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
    count = 0
    with tarfile.open(archive, "r:gz") as packed:
        members = [member for member in packed.getmembers() if member.isfile()]
        names = [member.name.removeprefix("./") for member in members]
        require(len(names) == len(set(names)), "duplicate inner archive member")
        require("evidence/ARCHIVE_SHA256" not in names, "self-hash unexpectedly archived")
        for member, name in zip(members, names, strict=True):
            require(name.startswith("evidence/"), f"unexpected inner member: {name}")
            sibling = root / PurePosixPath(name)
            require(sibling.is_file(), f"inner member lacks sibling: {name}")
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
            require(".." not in PurePosixPath(name).parts and not name.startswith("/"),
                    f"unsafe ZIP member: {name}")
        require(set(names) == set(extracted), "outer ZIP/extracted member-set mismatch")
        for info, name in zip(infos, names, strict=True):
            require(packed.read(info) == extracted[name].read_bytes(),
                    f"ZIP/extracted mismatch: {name}")
    require(len(infos) > 0, "empty outer ZIP")
    return len(infos)


def validate(
    artifact_root: Path,
    outer_zip: Path,
    source_sha: str,
    workflow_sha: str,
    manifest: list[tuple[str, str]] | None = None,
) -> dict[str, object]:
    root = artifact_root.resolve()
    outer = outer_zip.resolve()
    evidence = root / "evidence"
    inner = root / INNER_ARCHIVE
    require(evidence.is_dir(), f"missing evidence directory: {evidence}")
    require(outer.is_file(), f"missing raw artifact ZIP: {outer}")
    require(inner.is_file(), f"missing inner archive: {inner}")

    checkpoint = key_values(evidence / "checkpoint.txt")
    require(checkpoint.get("SOURCE_SHA") == source_sha, "wrong SOURCE_SHA")
    require(checkpoint.get("ACTUAL_HEAD") == source_sha, "wrong ACTUAL_HEAD")
    require(checkpoint.get("WORKFLOW_SHA") == workflow_sha, "wrong WORKFLOW_SHA")
    require(checkpoint.get("COLD_MODE") == "true", "COLD_MODE is not true")

    wanted_manifest = manifest if manifest is not None else expected_manifest(source_sha)
    measured_manifest: list[tuple[str, str]] = []
    for raw in (evidence / "source-blobs.sha256").read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (\S+)", raw)
        require(match is not None, f"bad source manifest line: {raw!r}")
        measured_manifest.append((match.group(1), match.group(2)))
    require(measured_manifest == wanted_manifest, "source blob manifest mismatch/order drift")
    paths = [path for _, path in wanted_manifest]
    require(
        (evidence / "overlay-paths.txt").read_text(encoding="utf-8").splitlines() == paths,
        "overlay path scope/order mismatch",
    )

    toolchain = (evidence / "toolchain.txt").read_text(encoding="utf-8")
    require(f"TOOLCHAIN_URL={TOOLCHAIN_URL}" in toolchain, "wrong toolchain URL")
    require(f"TOOLCHAIN_ASSET_SHA256={TOOLCHAIN_ASSET_SHA256}" in toolchain,
            "wrong toolchain digest")
    require(re.search(r"^[0-9a-f]{64}  .*/lean$", toolchain, re.MULTILINE) is not None,
            "missing Lean executable digest")
    require(re.search(r"^[0-9a-f]{64}  .*/lake$", toolchain, re.MULTILINE) is not None,
            "missing Lake executable digest")
    require("Lean (version 4.29.0-rc6" in toolchain, "wrong Lean version")
    require("Lake version " in toolchain, "missing Lake version")
    require((evidence / "mathlib.txt").read_text(encoding="utf-8").strip()
            == f"MATHLIB_SHA={MATHLIB_SHA}", "wrong Mathlib pin")
    require(f"LEAN_OVERLAY_TEXT_OK files={EXPECTED_FILES}" in
            (evidence / "text-guard.log").read_text(encoding="utf-8"),
            f"text guard did not cover {EXPECTED_FILES} files")
    require("LEAN_IMPORT_PREFIX_OK" in
            (evidence / "import-prefix-guard.log").read_text(encoding="utf-8"),
            "import-prefix guard did not pass")

    rows = stage_rows()
    ordered_stages = [stage for row in rows for stage in row[:2]]
    stages = parse_stage_times(evidence / "stages.txt", ordered_stages)
    measured_axioms: dict[str, list[list[str]]] = {}
    jobs: dict[str, int] = {}
    for focal_stage, audit_stage, module_path, count in rows:
        focal_text = (evidence / f"{focal_stage}.log").read_text(encoding="utf-8")
        lines = [line.strip() for line in focal_text.splitlines() if line.strip()]
        build = [line for line in lines if re.fullmatch(
            r"Build completed successfully \(\d+ jobs\)\.", line
        )]
        require(len(build) == 1 and lines[-1] == build[0],
                f"bad literal build sentinel: {focal_stage}")
        require(f"warning: {module_path}:" not in focal_text,
                f"new-module linter warning: {focal_stage}")
        jobs[focal_stage] = int(re.search(r"\((\d+) jobs\)", build[0]).group(1))
        audit_text = (evidence / f"{audit_stage}.log").read_text(encoding="utf-8")
        measured_axioms[audit_stage] = parse_axioms(audit_text, count, audit_stage)
    recorded_axioms = json.loads((evidence / "axioms.json").read_text(encoding="utf-8"))
    require(recorded_axioms == measured_axioms, "axioms.json differs from audit logs")
    require(sum(len(value) for value in measured_axioms.values()) == EXPECTED_AXIOMS,
            f"measured axiom total is not {EXPECTED_AXIOMS}")
    require((evidence / "FINAL_STATUS").read_text(encoding="utf-8")
            == "FINAL_STATUS=PASS\n", "FINAL_STATUS is not literal PASS")

    manifest_count = verify_sha256sums(root, evidence / "SHA256SUMS")
    archive_line = (evidence / "ARCHIVE_SHA256").read_text(encoding="utf-8").strip()
    match = re.fullmatch(rf"([0-9a-f]{{64}})  {re.escape(INNER_ARCHIVE)}", archive_line)
    require(match is not None, "malformed ARCHIVE_SHA256")
    inner_hash = digest(inner)
    require(inner_hash == match.group(1), "inner archive digest mismatch")
    inner_members = verify_inner_archive(root, inner)
    outer_members = verify_outer_zip(root, outer)

    return {
        "source_sha": source_sha,
        "workflow_sha": workflow_sha,
        "stages": stages,
        "jobs": jobs,
        "manifest_entries": manifest_count,
        "inner_members": inner_members,
        "outer_members": outer_members,
        "inner_archive_sha256": inner_hash.upper(),
        "outer_artifact_zip_sha256": digest(outer).upper(),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact-root", required=True, type=Path)
    parser.add_argument("--outer-zip", required=True, type=Path)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--workflow-sha", required=True)
    args = parser.parse_args()
    result = validate(
        args.artifact_root, args.outer_zip, args.source_sha, args.workflow_sha
    )
    print("STEP8B23_AE_COLD_EVIDENCE_OK")
    print(f"source_sha={result['source_sha']}")
    print(f"workflow_sha={result['workflow_sha']}")
    print(f"bricks={EXPECTED_BRICKS}")
    print(f"stages={2 * EXPECTED_BRICKS}")
    print(f"axiom_blocks={EXPECTED_AXIOMS}")
    print(f"manifest_entries={result['manifest_entries']}")
    print(f"inner_members={result['inner_members']}")
    print(f"outer_members={result['outer_members']}")
    print(f"inner_archive_sha256={result['inner_archive_sha256']}")
    print(f"outer_artifact_zip_sha256={result['outer_artifact_zip_sha256']}")
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
        print(f"STEP8B23_AE_COLD_EVIDENCE_FAIL: {error}")
        raise SystemExit(1)
