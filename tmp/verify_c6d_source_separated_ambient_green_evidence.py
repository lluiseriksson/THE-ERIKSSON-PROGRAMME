#!/usr/bin/env python3
"""Fail-closed verifier for the C6d source-carrier ambient Green cold gate."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile


SOURCE_SHA = "7e90203e8bfd1deb58d998fb5cdad0baab925af5"
RUNNER_REV = "c6d-source-separated-ambient-green-v4"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_SHA256 = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)
SOURCE_BLOBS_COUNT = 7
SOURCE_BLOBS_SHA256 = (
    "7F508F25E1C8C3656CCC923A69E190B5C6C14BD13DEC6FFD5EFDBBA75D0F3559"
)
NOTEBOOK_CELL_SOURCE_SHA256 = (
    "151D99D83F444D9F6662003C3FF3BF0B4A655E8842A2FEB97B5FAC665EBF4264"
)
SUCCESS_SENTINEL = "C6D_SOURCE_SEPARATED_AMBIENT_GREEN_EVIDENCE_OK"

MODULES = [
    "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreen",
    "BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepth",
    "BalabanCMP99Eq360C6dCanonicalAmbientCompletion",
]
AUDIT_STAGES = {
    MODULES[0]: "01_cmp99eq360c6dsourceseparatedambientgreen_audit",
    MODULES[1]: "02_cmp99eq360c6dsourceseparatedambientgreenzerodepth_audit",
    MODULES[2]: "03_cmp99eq360c6dcanonicalambientcompletion_audit",
}
EXPECTED_AXIOM_HEADERS = {MODULES[0]: 15, MODULES[1]: 10, MODULES[2]: 2}

BOOTSTRAP_STAGES = [
    "download_toolchain",
    "extract_toolchain",
    "lean_version",
    "lake_version",
    "clone",
    "checkout",
    "head",
    "overlay_text_guard",
    "import_prefix_guard",
    "lake_update",
    "mathlib_pin",
    "cache_get",
]
QUEUE_STAGES = [
    "01_cmp99eq360c6dsourceseparatedambientgreen_focal",
    "01_cmp99eq360c6dsourceseparatedambientgreen_audit",
    "02_cmp99eq360c6dsourceseparatedambientgreenzerodepth_focal",
    "02_cmp99eq360c6dsourceseparatedambientgreenzerodepth_audit",
    "03_cmp99eq360c6dcanonicalambientcompletion_focal",
    "03_cmp99eq360c6dcanonicalambientcompletion_audit",
    "04_c6d_source_green_yang_mills_core_root",
]

# Optional, fail-closed extensions used by wrappers that replace ``lake update``
# with exact package materialization.  The default verifier accepts neither
# extra package stages nor records without a stdout digest.
PACKAGE_MATERIALIZATION_NAMES: list[str] = []
MODE_RECORDS: dict[str, str] = {}
PAYLOAD_ONLY_ARCHIVE = False
TRANSCRIPT_HASH_STAGES: list[str] = []


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest().upper()


def safe_members(archive: tarfile.TarFile) -> list[tarfile.TarInfo]:
    members = archive.getmembers()
    for member in members:
        parts = Path(member.name).parts
        if member.name.startswith(("/", "\\")) or ".." in parts:
            raise RuntimeError(f"UNSAFE_ARCHIVE_MEMBER={member.name}")
        if not member.isdir() and not member.isfile():
            raise RuntimeError(f"NONREGULAR_ARCHIVE_MEMBER={member.name}")
    return members


def transcript_stage_output(transcript: str, stage: str) -> bytes:
    """Recover one child stdout exactly from the runner's streamed transcript."""
    command_marker = f"STAGE={stage} CMD="
    exit_marker = f"STAGE={stage} EXIT=0 SECONDS="
    if transcript.count(command_marker) != 1:
        raise RuntimeError(
            f"TRANSCRIPT_STAGE_COMMAND_COUNT_{stage}="
            f"{transcript.count(command_marker)} EXPECTED=1"
        )
    if transcript.count(exit_marker) != 1:
        raise RuntimeError(
            f"TRANSCRIPT_STAGE_EXIT_COUNT_{stage}="
            f"{transcript.count(exit_marker)} EXPECTED=1"
        )
    start = transcript.index(command_marker)
    start = transcript.find("\n", start)
    if start < 0:
        raise RuntimeError(f"TRANSCRIPT_STAGE_COMMAND_UNTERMINATED={stage}")
    start += 1
    end = transcript.index(exit_marker, start)
    streamed = transcript[start:end]
    # ``run`` emits child stdout with ``print(output)``.  Remove exactly the
    # newline added by print, retaining any newline already present in output.
    if not streamed.endswith("\n"):
        raise RuntimeError(f"TRANSCRIPT_STAGE_OUTPUT_UNTERMINATED={stage}")
    return streamed[:-1].encode("utf-8")


def executed_notebook_text(path: Path) -> str:
    if not path.is_file():
        raise RuntimeError(f"NOTEBOOK_NOT_FOUND={path}")
    notebook = json.loads(path.read_text(encoding="utf-8"))
    cells = notebook.get("cells")
    if not isinstance(cells, list):
        raise RuntimeError("NOTEBOOK_CELLS_NOT_LIST")
    code_cells = [cell for cell in cells if cell.get("cell_type") == "code"]
    if len(code_cells) != 1:
        raise RuntimeError(f"NOTEBOOK_CODE_CELL_COUNT={len(code_cells)}")
    cell = code_cells[0]
    source = cell.get("source")
    if isinstance(source, list):
        source_text = "".join(source)
    elif isinstance(source, str):
        source_text = source
    else:
        raise RuntimeError("NOTEBOOK_CELL_SOURCE_INVALID")
    source_sha = hashlib.sha256(source_text.encode()).hexdigest().upper()
    if source_sha != NOTEBOOK_CELL_SOURCE_SHA256:
        raise RuntimeError(
            f"NOTEBOOK_CELL_SOURCE_SHA256={source_sha} "
            f"EXPECTED={NOTEBOOK_CELL_SOURCE_SHA256}"
        )
    if cell.get("execution_count") is None:
        raise RuntimeError("NOTEBOOK_CELL_NOT_EXECUTED")
    chunks: list[str] = []
    for index, output in enumerate(cell.get("outputs", [])):
        output_type = output.get("output_type")
        if output_type == "error":
            raise RuntimeError(f"NOTEBOOK_ERROR_OUTPUT_{index}={output!r}")
        if output_type == "stream":
            text = output.get("text")
            if isinstance(text, list):
                chunks.append("".join(text))
            elif isinstance(text, str):
                chunks.append(text)
            else:
                raise RuntimeError(f"NOTEBOOK_STREAM_TEXT_{index}_INVALID")
        elif output_type not in {"display_data", "execute_result"}:
            raise RuntimeError(f"NOTEBOOK_OUTPUT_TYPE_{index}={output_type!r}")
    result = "".join(chunks)
    for token in (
        "FINAL_STATUS=PASS",
        "LAUNCHER_EXIT=0",
        "RUNTIME_RETAINED_FOR_EVIDENCE_DOWNLOAD=1",
    ):
        if result.count(token) != 1:
            raise RuntimeError(
                f"NOTEBOOK_TOKEN_COUNT_{token}={result.count(token)} EXPECTED=1"
            )
    for forbidden in ("FINAL_STATUS=FAIL", "sorryAx", "ofReduceBool"):
        if forbidden in result:
            raise RuntimeError(f"NOTEBOOK_FORBIDDEN_TOKEN={forbidden}")
    return result


def audit_notebook_transcript(text: str, evidence_sha: str, archive_sha: str) -> None:
    printed_evidence = re.findall(
        r"^EVIDENCE_SHA256=([0-9a-f]{64})$", text, flags=re.MULTILINE
    )
    printed_archive = re.findall(
        r"^EVIDENCE_ARCHIVE_SHA256=([0-9a-f]{64})$", text, flags=re.MULTILINE
    )
    if printed_evidence != [evidence_sha.lower()]:
        raise RuntimeError(
            f"NOTEBOOK_EVIDENCE_SHA256={printed_evidence!r} "
            f"EXPECTED={[evidence_sha.lower()]!r}"
        )
    if printed_archive != [archive_sha.lower()]:
        raise RuntimeError(
            f"NOTEBOOK_ARCHIVE_SHA256={printed_archive!r} "
            f"EXPECTED={[archive_sha.lower()]!r}"
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    parser.add_argument("notebook", type=Path)
    args = parser.parse_args()
    archive_path = args.archive.resolve()
    notebook_path = args.notebook.resolve()
    if not archive_path.is_file():
        raise RuntimeError(f"ARCHIVE_NOT_FOUND={archive_path}")

    with tarfile.open(archive_path, "r:gz") as archive:
        members = safe_members(archive)
        evidence_members = [
            member for member in members if member.name.endswith("/evidence.json")
        ]
        if len(evidence_members) != 1:
            raise RuntimeError(
                f"EVIDENCE_JSON_COUNT={len(evidence_members)} EXPECTED=1"
            )
        regular_payloads: dict[str, bytes] = {}
        for member in members:
            if not member.isfile():
                continue
            if member.name in regular_payloads:
                raise RuntimeError(f"DUPLICATE_REGULAR_MEMBER={member.name}")
            extracted = archive.extractfile(member)
            if extracted is None:
                raise RuntimeError(f"UNREADABLE_REGULAR_MEMBER={member.name}")
            regular_payloads[member.name] = extracted.read()
        evidence_name = evidence_members[0].name
        payload = json.loads(regular_payloads[evidence_name])

    expected_scalars = {
        "runner_rev": RUNNER_REV,
        "source_sha": SOURCE_SHA,
        "mathlib_sha": MATHLIB_SHA,
        "toolchain_asset_sha256": TOOLCHAIN_SHA256,
        "status": "PASS",
    }
    for key, expected in expected_scalars.items():
        actual = payload.get(key)
        if actual != expected:
            raise RuntimeError(f"{key.upper()}={actual!r} EXPECTED={expected!r}")

    source_blobs = payload.get("source_blobs")
    if not isinstance(source_blobs, dict):
        raise RuntimeError("SOURCE_BLOBS_NOT_DICT")
    if len(source_blobs) != SOURCE_BLOBS_COUNT:
        raise RuntimeError(
            f"SOURCE_BLOBS_COUNT={len(source_blobs)} EXPECTED={SOURCE_BLOBS_COUNT}"
        )
    canonical_blobs = json.dumps(source_blobs, sort_keys=True, separators=(",", ":"))
    measured_blobs = hashlib.sha256(canonical_blobs.encode()).hexdigest().upper()
    if measured_blobs != SOURCE_BLOBS_SHA256:
        raise RuntimeError(
            f"SOURCE_BLOBS_SHA256={measured_blobs} EXPECTED={SOURCE_BLOBS_SHA256}"
        )

    records = payload.get("records")
    if not isinstance(records, list):
        raise RuntimeError("RECORDS_NOT_LIST")
    for index, record in enumerate(records):
        if not isinstance(record, dict):
            raise RuntimeError(f"RECORD_{index}_NOT_DICT")
        stage = record.get("stage")
        expected_mode = MODE_RECORDS.get(stage) if isinstance(stage, str) else None
        expected_keys = (
            {"stage", "exit", "seconds", "mode"}
            if expected_mode is not None
            else {"stage", "exit", "seconds", "output_sha256"}
        )
        if set(record) != expected_keys:
            raise RuntimeError(f"RECORD_{index}_KEYS={sorted(record)!r}")
        if type(record["exit"]) is not int or record["exit"] != 0:
            raise RuntimeError(f"RECORD_{index}_EXIT={record['exit']!r}")
        if not isinstance(record["seconds"], (int, float)) or record["seconds"] < 0:
            raise RuntimeError(f"RECORD_{index}_SECONDS={record['seconds']!r}")
        if expected_mode is not None:
            if record["mode"] != expected_mode:
                raise RuntimeError(
                    f"RECORD_{index}_MODE={record['mode']!r} EXPECTED={expected_mode!r}"
                )
        elif not re.fullmatch(r"[0-9a-f]{64}", record["output_sha256"]):
            raise RuntimeError(f"RECORD_{index}_OUTPUT_SHA256_INVALID")

    stages = [record["stage"] for record in records]
    bootstrap_variants = [
        BOOTSTRAP_STAGES,
        BOOTSTRAP_STAGES[:1]
        + ["apt_update", "install_zstd"]
        + BOOTSTRAP_STAGES[1:],
    ]
    if PACKAGE_MATERIALIZATION_NAMES:
        package_stages = [
            f"package_{operation}_{name}"
            for name in PACKAGE_MATERIALIZATION_NAMES
            for operation in ("init", "remote", "fetch", "checkout", "pin")
        ]
        expanded: list[list[str]] = []
        for bootstrap in bootstrap_variants:
            lake_update_index = bootstrap.index("lake_update")
            expanded.append(
                bootstrap[:lake_update_index]
                + package_stages
                + bootstrap[lake_update_index:]
            )
        bootstrap_variants.extend(expanded)
    sanctioned = [bootstrap + QUEUE_STAGES for bootstrap in bootstrap_variants]
    if stages not in sanctioned:
        raise RuntimeError(f"UNSANCTIONED_STAGE_SEQUENCE={stages!r}")

    notebook_text = executed_notebook_text(notebook_path)
    prefix = evidence_name.rsplit("/", 1)[0]
    expected_names = {evidence_name}
    stage_members: dict[str, str] = {}
    if not PAYLOAD_ONLY_ARCHIVE:
        for index, stage in enumerate(stages):
            name = f"{prefix}/{index:03d}-{stage}.stdout"
            expected_names.add(name)
            stage_members[stage] = name
    actual_names = set(regular_payloads)
    if actual_names != expected_names:
        raise RuntimeError(
            f"ARCHIVE_MEMBER_DELTA_MISSING={sorted(expected_names-actual_names)!r} "
            f"UNEXPECTED={sorted(actual_names-expected_names)!r}"
        )

    transcript_bodies: dict[str, bytes] = {}
    for record in records:
        stage = record["stage"]
        if PAYLOAD_ONLY_ARCHIVE:
            if stage not in TRANSCRIPT_HASH_STAGES:
                continue
            body = transcript_stage_output(notebook_text, stage)
            transcript_bodies[stage] = body
        else:
            body = regular_payloads[stage_members[stage]]
            body = (
                body.decode("utf-8")
                .replace("\r\n", "\n")
                .replace("\r", "\n")
                .encode("utf-8")
            )
        measured = hashlib.sha256(body).hexdigest()
        if "output_sha256" in record and measured != record["output_sha256"]:
            raise RuntimeError(
                f"STAGE_OUTPUT_SHA256_{stage}={measured} "
                f"EXPECTED={record['output_sha256']}"
            )

    for module in MODULES:
        stage = AUDIT_STAGES[module]
        body = (
            transcript_bodies[stage]
            if PAYLOAD_ONLY_ARCHIVE
            else regular_payloads[stage_members[stage]]
        ).decode("utf-8")
        compact = re.sub(r"\s+", "", body)
        blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
        expected = EXPECTED_AXIOM_HEADERS[module]
        if len(blocks) != expected:
            raise RuntimeError(
                f"ARCHIVE_AXIOM_HEADER_COUNT_{module}={len(blocks)} EXPECTED={expected}"
            )
        for block in blocks:
            names = {name for name in block.split(",") if name}
            if not names.issubset({"propext", "Classical.choice", "Quot.sound"}):
                raise RuntimeError(
                    f"ARCHIVE_FORBIDDEN_AXIOMS_{module}={sorted(names)!r}"
                )
        for forbidden in ("sorryAx", "ofReduceBool"):
            if forbidden in body:
                raise RuntimeError(
                    f"ARCHIVE_FORBIDDEN_AXIOM_TOKEN_{module}={forbidden}"
                )

    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    evidence_sha = hashlib.sha256(canonical.encode()).hexdigest().upper()
    archive_sha = sha256(archive_path)
    audit_notebook_transcript(notebook_text, evidence_sha, archive_sha)
    total_seconds = sum(float(record["seconds"]) for record in records)
    print(SUCCESS_SENTINEL)
    print(f"SOURCE_SHA={SOURCE_SHA}")
    print(f"RUNNER_REV={RUNNER_REV}")
    print(f"RECORDS={len(records)}")
    print(f"TOTAL_STAGE_SECONDS={total_seconds:.3f}")
    print(f"EVIDENCE_SHA256={evidence_sha}")
    print(f"ARCHIVE_SHA256={archive_sha}")
    print(f"NOTEBOOK_SHA256={sha256(notebook_path)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
