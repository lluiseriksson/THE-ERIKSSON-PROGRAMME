#!/usr/bin/env python3
"""Verify the physical-residue cold gate and preserve its exact child outputs.

This is an evidence-only operation: it never invokes Lean, Lake, or Git.
The raw tmux stream must have been attached before the buffered focal output
was printed. Removing terminal CRLF and the runner's one print-added newline
is accepted only when the recovered bytes match the original recorded hash.
The runner's original archive is retained unchanged in the optional bundle.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import tarfile


SOURCE = "c9f4b725313dd879ae3ce6e99c844ce1d2f8b968"
REV = "cmp99-physical-residue-endpoint-dictionary-cold-v1"
MATHLIB = "07642720480157414db592fa85b626dafb71355b"
ASSET = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionary.lean":
        "6b6e760a4af04bd0f0b6438051f7922e956f3b7142dabe464785bf8eaea9e0c7",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalResidueEndpointDictionaryAudit.lean":
        "8fabe6f585eaeec19d292695596ddc0b2c468d72cc304ea07e75e8d86dbbd109",
}
FOCAL = "physical_residue_endpoint_dictionary_focal"
AUDIT = "physical_residue_endpoint_dictionary_audit"
NAMES = {
    "YangMills.RG.cmp99SourceGeneratedFlatPhysicalResidueEndpointBase",
    "YangMills.RG.cmp99SourceGeneratedFlatPhysicalResidueEndpointBase_cast",
    "YangMills.RG.cmp89Eq251LatticeL1Length_centered_generatedPhysicalResidueEndpoint_eq",
    "YangMills.RG.cmp89SignedLatticeL1ExponentialWeight_centered_generatedPhysicalResidueEndpoint_eq",
    "YangMills.RG.cmp89SignedLatticeL1ExponentialWeight_centered_generatedPhysicalResidueEndpoint_le_owner",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LIMIT = 32 * 1024 * 1024


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def bounded_read(path: Path) -> bytes:
    require(path.is_file() and path.stat().st_size <= LIMIT, "missing/oversized: " + str(path))
    return path.read_bytes()


def recover_output(stream: str, stage: str, expected_hash: str, *, first: bool) -> bytes:
    end_marker = "STAGE=" + stage + " EXIT="
    require(stream.count(end_marker) == 1, "missing/duplicate exit marker: " + stage)
    before = stream.split(end_marker, 1)[0]
    start_marker = "STAGE=" + stage + " CMD="
    if start_marker in before:
        require(before.count(start_marker) == 1, "duplicate command: " + stage)
        segment = before.split(start_marker, 1)[1].split("\n", 1)[1]
    else:
        require(first, "missing command marker: " + stage)
        segment = before
    require(segment.endswith("\n"), "missing print delimiter: " + stage)
    output = segment[:-1].encode("utf-8")
    require(digest(output) == expected_hash, "child output hash mismatch: " + stage)
    return output


def verify(archive_path: Path, raw_path: Path) -> dict[str, bytes]:
    original = bounded_read(archive_path)
    terminal = bounded_read(raw_path)
    with tarfile.open(archive_path, "r:gz") as tf:
        files = [m for m in tf.getmembers() if m.isfile()]
        require(len(files) == 1 and files[0].name.endswith("/evidence.json"),
                "unexpected original archive layout")
        require(files[0].size <= LIMIT, "oversized evidence JSON")
        source = tf.extractfile(files[0])
        require(source is not None, "unreadable evidence JSON")
        raw_json = source.read()
    data = json.loads(raw_json)
    for key, expected in {
        "source_sha": SOURCE, "runner_rev": REV, "mathlib_sha": MATHLIB,
        "toolchain_asset_sha256": ASSET, "source_blobs": BLOBS, "status": "PASS",
    }.items():
        require(data.get(key) == expected, "evidence mismatch: " + key)
    records = data.get("records")
    require(isinstance(records, list) and bool(records), "missing stage records")
    indexed = {r["stage"]: r for r in records}
    require(len(indexed) == len(records), "duplicate stage")
    required = {"lean_version", "lake_version", "clone", "checkout", "head",
                "overlay_text_guard", "import_prefix_guard", "lake_update",
                "mathlib_pin", "cache_get", FOCAL, AUDIT}
    require(required <= set(indexed), "missing required stage: " + str(required - set(indexed)))
    for record in records:
        require(record.get("exit") == 0, "nonzero child exit: " + record["stage"])
        elapsed = record.get("seconds")
        require(isinstance(elapsed, (float, int)) and math.isfinite(elapsed) and elapsed >= 0,
                "invalid elapsed time")
        require(re.fullmatch(r"[0-9a-f]{64}", record.get("output_sha256", "")) is not None,
                "invalid output hash")
    stream = terminal.decode("utf-8").replace("\r\n", "\n")
    require("FINAL_STATUS=PASS" in stream, "no final PASS in captured runner output")
    focal = recover_output(stream, FOCAL, indexed[FOCAL]["output_sha256"], first=True)
    audit = recover_output(stream, AUDIT, indexed[AUDIT]["output_sha256"], first=False)
    compact = re.sub(r"\s+", "", audit.decode("utf-8"))
    require(not any(x in compact for x in ("sorryAx", "ofReduceBool")), "forbidden axiom")
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    empty = re.findall(r"'([^']+)'doesnotdependonanyaxioms", compact)
    seen = [name for name, _ in blocks] + empty
    require(len(seen) == len(NAMES) and set(seen) == NAMES, "exact axiom declaration gate failed")
    for name, body in blocks:
        require(set(filter(None, body.split(","))) <= ALLOWED, "unexpected axiom: " + name)
    print("PHYSICAL_RESIDUE_COLD_EVIDENCE_VERIFIED", flush=True)
    print("SOURCE_SHA=" + SOURCE, flush=True)
    for stage in (FOCAL, AUDIT):
        print(json.dumps(indexed[stage], sort_keys=True), flush=True)
    print("AXIOM_DECLARATIONS=5/5", flush=True)
    print("ORIGINAL_ARCHIVE_SHA256=" + digest(original), flush=True)
    print("EVIDENCE_JSON_SHA256=" + digest(raw_json), flush=True)
    return {"original-evidence.tar.gz": original, "evidence.json": raw_json,
            "terminal.raw": terminal, "focal.log": focal, "audit.log": audit}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    parser.add_argument("terminal", type=Path)
    parser.add_argument("--package", type=Path)
    args = parser.parse_args()
    files = verify(args.archive, args.terminal)
    if args.package:
        require(not args.package.exists(), "refusing to overwrite evidence package directory")
        bundle = args.package.with_suffix(".tar.gz")
        require(not bundle.exists(), "refusing to overwrite evidence archive")
        args.package.mkdir(parents=True)
        for name, content in files.items():
            (args.package / name).write_bytes(content)
        manifest = {name: digest(content) for name, content in sorted(files.items())}
        (args.package / "SHA256.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        with tarfile.open(bundle, "w:gz") as tf:
            tf.add(args.package, arcname=args.package.name)
        print("VERIFIED_BUNDLE=" + str(bundle), flush=True)
        print("VERIFIED_BUNDLE_SHA256=" + digest(bounded_read(bundle)), flush=True)


if __name__ == "__main__":
    main()
