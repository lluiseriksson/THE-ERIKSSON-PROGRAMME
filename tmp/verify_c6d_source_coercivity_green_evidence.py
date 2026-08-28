#!/usr/bin/env python3
"""Fail-closed verifier for the C6d source coercivity/Green cold archive."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile


SOURCE_SHA = "2bb3eb7325b621954a7132d0a8bab3ce2c1bdf24"
RUNNER_REV = "c6d-source-coercivity-green-v1"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_SHA256 = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)
SOURCE_BLOBS_COUNT = 21
SOURCE_BLOBS_SHA256 = (
    "77E278086CC1F952F5C1855D88E1CE7EC4A51725F219F93D900856B51A301D66"
)
NOTEBOOK_CELL_SOURCE_SHA256 = (
    "E841A3887E4F71426E22FC890101C9CF3AE04F4BCB2171B3B7D626A24C9C64D4"
)

MODULES = [
    "BalabanCMP99SourcePoincarePositiveRadiusReachability",
    "BalabanCMP99SourceWeightedGaugePrecisionDictionary",
    "BalabanCMP99Eq360WeightedPrecisionRealSlice",
    "BalabanCMP99SourceActiveRegionTerminalCoercivity",
    "BalabanCMP99Eq360C6dLaplacianRetainedExtension",
    "BalabanCMP99Eq360C6dLocalizedRetainedPrecision",
    "BalabanCMP99Eq360C6dSourceFixedInput",
    "BalabanCMP99Eq360C6dSourceTerminalCoercivity",
    "BalabanCMP99Eq360C6dSourceTerminalCoercivityReachability",
    "BalabanCMP99Eq360C6dSourceBaselineGreen",
]
EXPECTED_AXIOM_HEADERS = [9, 3, 1, 8, 6, 30, 11, 3, 1, 8]

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


def expected_queue_stages() -> list[str]:
    result = [
        "c6d_source_coercivity_green_materialize_dependencies",
        "c6d_source_coercivity_green_prepare_build_dirs",
    ]
    for index, module in enumerate(MODULES, start=1):
        stem = f"c6d_source_coercivity_green_{index:02d}_{module.lower()}"
        result.extend([stem + "_source", stem + "_audit"])
    result.append("c6d_source_coercivity_green_root")
    return result


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
        if output_type != "stream":
            raise RuntimeError(
                f"NOTEBOOK_OUTPUT_TYPE_{index}={output_type!r} EXPECTED='stream'"
            )
        text = output.get("text")
        if isinstance(text, list):
            chunks.append("".join(text))
        elif isinstance(text, str):
            chunks.append(text)
        else:
            raise RuntimeError(f"NOTEBOOK_STREAM_TEXT_{index}_INVALID")
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


def audit_notebook_transcript(
    text: str, evidence_sha: str, archive_sha: str
) -> None:
    # Colab persists only the tail of very long streaming outputs.  The exact
    # stage sequence, outputs and axiom blocks are therefore audited from the
    # archive below; the notebook is authoritative for the executed cell,
    # terminal sentinel and the two printed content hashes.
    printed_evidence = re.findall(
        r"^EVIDENCE_SHA256=([0-9a-f]{64})$", text, flags=re.MULTILINE
    )
    printed_archive = re.findall(
        r"^EVIDENCE_ARCHIVE_SHA256=([0-9a-f]{64})$",
        text,
        flags=re.MULTILINE,
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
    if not archive_path.is_file():
        raise RuntimeError(f"ARCHIVE_NOT_FOUND={archive_path}")
    notebook_path = args.notebook.resolve()

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
        raw = regular_payloads[evidence_name]

    payload = json.loads(raw)
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
    source_blobs_canonical = json.dumps(
        source_blobs, sort_keys=True, separators=(",", ":")
    )
    source_blobs_sha = hashlib.sha256(
        source_blobs_canonical.encode()
    ).hexdigest().upper()
    if source_blobs_sha != SOURCE_BLOBS_SHA256:
        raise RuntimeError(
            f"SOURCE_BLOBS_SHA256={source_blobs_sha} "
            f"EXPECTED={SOURCE_BLOBS_SHA256}"
        )

    records = payload.get("records")
    if not isinstance(records, list):
        raise RuntimeError("RECORDS_NOT_LIST")
    for index, record in enumerate(records):
        if not isinstance(record, dict):
            raise RuntimeError(f"RECORD_{index}_NOT_DICT")
        if set(record) != {"stage", "exit", "seconds", "output_sha256"}:
            raise RuntimeError(f"RECORD_{index}_KEYS={sorted(record)!r}")
        if not isinstance(record["stage"], str):
            raise RuntimeError(f"RECORD_{index}_STAGE_NOT_STRING")
        if type(record["exit"]) is not int:
            raise RuntimeError(f"RECORD_{index}_EXIT_NOT_INT")
        if not isinstance(record["seconds"], (int, float)) or record["seconds"] < 0:
            raise RuntimeError(f"RECORD_{index}_SECONDS={record['seconds']!r}")
        if not isinstance(record["output_sha256"], str) or not re.fullmatch(
            r"[0-9a-f]{64}", record["output_sha256"]
        ):
            raise RuntimeError(
                f"RECORD_{index}_OUTPUT_SHA256={record['output_sha256']!r}"
            )
    stages = [record.get("stage") for record in records]
    exits = [record.get("exit") for record in records]
    if any(exit_code != 0 for exit_code in exits):
        bad = [record for record in records if record.get("exit") != 0]
        raise RuntimeError(f"NONZERO_STAGE={bad!r}")

    queue_stages = expected_queue_stages()
    sanctioned_stage_lists = [
        BOOTSTRAP_STAGES + queue_stages,
        BOOTSTRAP_STAGES[:1]
        + ["apt_update", "install_zstd"]
        + BOOTSTRAP_STAGES[1:]
        + queue_stages,
    ]
    if stages not in sanctioned_stage_lists:
        raise RuntimeError(f"UNSANCTIONED_STAGE_SEQUENCE={stages!r}")

    evidence_prefix = evidence_name.rsplit("/", 1)[0]
    expected_regular_names = {
        evidence_name,
        *(f"{evidence_prefix}/{stage}.stdout" for stage in stages),
    }
    actual_regular_names = set(regular_payloads)
    missing_regular = sorted(expected_regular_names - actual_regular_names)
    unexpected_regular = sorted(actual_regular_names - expected_regular_names)
    if missing_regular:
        raise RuntimeError(f"MISSING_REGULAR_MEMBERS={missing_regular!r}")
    if unexpected_regular:
        raise RuntimeError(f"UNEXPECTED_REGULAR_MEMBERS={unexpected_regular!r}")
    for record in records:
        stage = record["stage"]
        member_name = f"{evidence_prefix}/{stage}.stdout"
        measured = hashlib.sha256(regular_payloads[member_name]).hexdigest()
        if measured != record["output_sha256"]:
            raise RuntimeError(
                f"STAGE_OUTPUT_SHA256_{stage}={measured} "
                f"EXPECTED={record['output_sha256']}"
            )

    for index, (module, expected) in enumerate(
        zip(MODULES, EXPECTED_AXIOM_HEADERS, strict=True), start=1
    ):
        stage = f"c6d_source_coercivity_green_{index:02d}_{module.lower()}_audit"
        member_name = f"{evidence_prefix}/{stage}.stdout"
        body = regular_payloads[member_name].decode("utf-8")
        blocks = re.findall(
            r"depends on axioms:\s*\[(.*?)\]", body, flags=re.DOTALL
        )
        pure = body.count("does not depend on any axioms")
        actual_headers = len(blocks) + pure
        if actual_headers != expected:
            raise RuntimeError(
                f"ARCHIVE_AXIOM_HEADER_COUNT_{module}={actual_headers} "
                f"EXPECTED={expected}"
            )
        for block in blocks:
            names = {name.strip() for name in block.replace("\n", " ").split(",")}
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
    notebook_text = executed_notebook_text(notebook_path)
    audit_notebook_transcript(notebook_text, evidence_sha, archive_sha)
    total_seconds = sum(float(record.get("seconds", 0.0)) for record in records)
    print("C6D_SOURCE_COERCIVITY_GREEN_EVIDENCE_OK")
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
