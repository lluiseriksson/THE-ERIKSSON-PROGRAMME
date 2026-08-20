#!/usr/bin/env python3
"""Fail-closed audit of the single-cell P0--P9 Colab transcript.

This checker does not compile Lean.  It verifies that an executed notebook is
the output of the immutable launcher and that the runner itself reported a
complete PASS for the exact 39-file source checkpoint.  A green transcript is
still intermediate compiler evidence, not a terminal hRpoly result.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
PATHS = ROOT / "tmp" / "P0-P9-SCRATCH-PATHS.txt"
SOURCE_SHA = "1b98e644347a96530b8f2755d67febc132cb9774"
RUNNER_SHA256 = "34296ef8601ebaadd5de7a64ec5af7c763ca3c44319a89ad9e26ec7fd6fd5126"
BASE_RUNNER_SHA256 = "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
PATHS_SHA256 = "fec594c0fba52e14f8cc1e1ba886202fcdf2e425de2c93e56dbf59feebb2fa61"
MANIFEST_SHA256 = "5ce25f62ef483caa67021335f0d513f8cd32a24089fa3d968300fe2ca6244d54"
RUNNER_REV = "p0-p9-prefix-combes-thomas-v55"
SUPPORTED_TRANSCRIPTS = {
    (
        "84eb07b5d1f2c3d7f245230a25846065b745a38e",
        "p0-p9-prefix-combes-thomas-v34",
    ): {
        "runner_sha256":
            "d6c06a8206a99e9538ac401e489fb7e5e6c300fe44dfd7e15c3bc6fca2311abb",
        "manifest_sha256":
            "e75af26bbbce875b13cab3a4403486bbf051457b4283152ad2c9bbe210137c91",
        "overlay_files": "42",
    },
    (
        "909a73cf87ff51486f9f460890a08f2efbe383ec",
        "p0-p9-prefix-combes-thomas-v35",
    ): {
        "runner_sha256":
            "8fa00df57a722f7e6babe955afbfac9fb2f88b01433f28e7c418fc85324c71da",
        "manifest_sha256":
            "da4b48eb37ceec6252c6e1f4ca5e2cf3154a8a7b15e4d9533e124e3c8ec5cffd",
        "overlay_files": "43",
    },
    (
        "afedb7b5d20e65a9b646255d9253a680b3202963",
        "p0-p9-prefix-combes-thomas-v36",
    ): {
        "runner_sha256":
            "b6211d78e90e90dfbb12782f475bc6abd34cb49e6c6e4ed476b59d194c44cef4",
        "manifest_sha256":
            "a4bba8a118a7286ee3f664d1a56c3d443befe8a86a835d6b979ca34cb3dc63e3",
        "overlay_files": "43",
    },
    (
        "c2340f8a09a7e77451d3d19e9b97e7f5ac7dc7e3",
        "p0-p9-prefix-combes-thomas-v37",
    ): {
        "runner_sha256":
            "63e6ae81121715211cd19bcbfaf119dd6ec9ff78284ada233d5bc4a5926f3b09",
        "manifest_sha256":
            "7f5b3f8e5dd0bd67fd575243b857d31d9883662b112cae0a97b98b7b64223af5",
        "overlay_files": "43",
    },
    (
        "00fba3862900059c0584697e814fb9f8ff18e687",
        "p0-p9-prefix-combes-thomas-v38",
    ): {
        "runner_sha256":
            "c725b36e63b1d5b1137c555dd9d977e9d8919cbc0ea3ad6c124ec593063a07d1",
        "manifest_sha256":
            "3fc7833495a8b1f6069d289ab08a5e2e208e89514b78a07bc3b07e71b0e6fc5e",
        "overlay_files": "43",
    },
    (
        "bc2ff22c518158bafc2be5f30dc630dc61c2065b",
        "p0-p9-prefix-combes-thomas-v39",
    ): {
        "runner_sha256":
            "198bb1e1b6832f3c859106516a5e7b3b639fd566c0c6e5a34467b2f4aaaed1d4",
        "manifest_sha256":
            "81981fae2c447664ee6c1ea42162984951d61141f22547f9419111b07d9b4caa",
        "overlay_files": "43",
    },
    (
        "621020110a3b2c445eebe68b09c974b13ed64978",
        "p0-p9-prefix-combes-thomas-v40",
    ): {
        "runner_sha256":
            "1a2e10bb123ad712a722fa3acf7ae819d0b849e75114646cdecbb8d89cf22fc2",
        "manifest_sha256":
            "035a25c14ae04079131734ea1951b0bf9163a2d8d47100888fc73f9c7c3860f2",
        "overlay_files": "43",
    },
    (
        "b64da7c6586f10354083eacc176e03d626647fc2",
        "p0-p9-prefix-combes-thomas-v41",
    ): {
        "runner_sha256":
            "83f4fe4c85b302f0ebe62504b282a706b5a9583c85d7d487a35af75258b138b1",
        "manifest_sha256":
            "36b12f7f9de76b24b188d9efd68c861a40551d5dafa493f2a71fd043606854e2",
        "overlay_files": "43",
    },
    (
        "d5c704c4e671336d5a220f7ed711170766a9ee97",
        "p0-p9-prefix-combes-thomas-v44",
    ): {
        "runner_sha256":
            "9f4f324458c5a28d363fb5c94bee463ef978a7f904d315ae051a436fd906c9c5",
        "manifest_sha256":
            "bd0f88c1ef87082cff16a7f1ac3eee440f92f8d846835ed6698be02a5ee52238",
        "overlay_files": "43",
    },
    (
        "6bbb3e08478795a83a2cd953f213475d630f2fba",
        "p0-p9-prefix-combes-thomas-v45",
    ): {
        "runner_sha256":
            "3707e52d0f3999242aaf20375d5c7f816962a723a4d30c143ccce040bd3c07f8",
        "manifest_sha256":
            "62e29687a52d7cefdc0e4998767f0d648a030ed4e33f5bd52e85ebac6c5f1c87",
        "overlay_files": "44",
    },
    (SOURCE_SHA, RUNNER_REV): {
        "runner_sha256": RUNNER_SHA256,
        "manifest_sha256": MANIFEST_SHA256,
        "overlay_files": "44",
    },
}
P0_SOURCE_STAGE = "p0_p9_01_p0canonicalprefixtower"
P0_AUDIT_STAGE = "p0_p9_02_p0canonicalprefixtoweraudit"
P0_AXIOM_HEADERS = 10
EXPECTED_AXIOM_BLOCKS = 199
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AUDIT_AXIOM_COUNTS = {
    "tmp/P0CanonicalPrefixTowerAudit.lean": 10,
    "tmp/P1CoefficientMonotonicityAudit.lean": 8,
    "tmp/P2SourceCoefficientCoercivityAudit.lean": 26,
    "tmp/P2bEffectiveQuadraticAudit.lean": 10,
    "tmp/P2cCoarseCovarianceAudit.lean": 24,
    "tmp/P3ScalarRecurrenceAudit.lean": 9,
    "tmp/P3BlockGaussianAlgebraAudit.lean": 2,
    "tmp/P3TypedSchurBracketsAudit.lean": 8,
    "tmp/P3TypedGreenInverseAudit.lean": 8,
    "tmp/P3SourceStepCoisometryAudit.lean": 2,
    "tmp/P3PhysicalScalarSpecializationAudit.lean": 4,
    "tmp/P3PhysicalOperatorDictionaryAudit.lean": 3,
    "tmp/P3PhysicalGreenRecurrenceAudit.lean": 3,
    "tmp/P3PhysicalGreenRecurrenceAggregateAudit.lean": 18,
    "tmp/P4aPhysicalBaseAudit.lean": 12,
    "tmp/P4bFiniteTelescopingAudit.lean": 14,
    "tmp/P5PhysicalGreenScaleDictionaryAudit.lean": 14,
    "tmp/P7SourceSeparatedAmbientPrefixPrecisionAudit.lean": 8,
    "tmp/P8SourceSeparatedRegionalPrefixGreenAudit.lean": 5,
    "tmp/P9SourceSeparatedPrefixCombesThomasAudit.lean": 12,
}
REQUIRED_CORE_STAGES = {
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
    "p0_p9_static_gate",
    "p0_p9_static_selftest",
    "p0_p9_p2b_algebra_repro",
    "p0_p9_p3_algebra_repro",
    "p0_p9_p3_typed_averaging_repro",
    "p0_p9_p3_typed_green_inverse_repro",
    "p0_p9_p3_physical_dictionary_repro",
    "p0_p9_materialize_project_prerequisites",
    "p0_p9_materialize_p7_p9_project_prerequisites",
    "p0_p9_prepare_scratch_build_dir",
}
P0_REQUIRED_CORE_STAGES = REQUIRED_CORE_STAGES - {
    # Materialized only after the P0--P5 prefix has passed; it cannot be a
    # prerequisite for accepting the earlier P0 source/audit pair.
    "p0_p9_materialize_p7_p9_project_prerequisites",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def output_text(notebook: dict[str, object]) -> tuple[str, int]:
    cells = notebook.get("cells")
    if not isinstance(cells, list):
        raise ValueError("notebook cells missing")
    evidenced = 0
    chunks: list[str] = []
    for cell in cells:
        if not isinstance(cell, dict) or cell.get("cell_type") != "code":
            continue
        outputs = cell.get("outputs", [])
        if not isinstance(outputs, list):
            raise ValueError("code-cell outputs malformed")
        # Colab's GitHub-backed "Download .ipynb" export can preserve the
        # complete output transcript while normalizing `execution_count` to
        # null.  The durable evidence is the output-bearing cell itself, not
        # that presentation-only counter.
        if outputs:
            evidenced += 1
        for output in outputs:
            if not isinstance(output, dict):
                raise ValueError("output entry malformed")
            if output.get("output_type") == "stream":
                text = output.get("text", "")
                chunks.extend(text if isinstance(text, list) else [str(text)])
            elif output.get("output_type") == "error":
                chunks.append("\n".join(map(str, output.get("traceback", []))))
    return "".join(chunks), evidenced


def expected_queue_stages() -> set[str]:
    payload = PATHS.read_bytes()
    if sha256(payload) != PATHS_SHA256:
        raise ValueError("local immutable path-list digest drift")
    paths = [line for line in payload.decode("utf-8-sig").splitlines() if line]
    if len(paths) != 39 or len(set(paths)) != 39:
        raise ValueError(f"local immutable path-list scope={len(paths)}/{len(set(paths))}")
    result: set[str] = set()
    for index, relative in enumerate(paths, start=1):
        stem = Path(relative).stem
        suffix = re.sub(r"[^A-Za-z0-9]+", "_", stem).lower()
        result.add(f"p0_p9_{index:02d}_{suffix}")
    return result


def expected_audit_stages() -> dict[str, int]:
    payload = PATHS.read_bytes()
    if sha256(payload) != PATHS_SHA256:
        raise ValueError("local immutable path-list digest drift")
    paths = [line for line in payload.decode("utf-8-sig").splitlines() if line]
    if set(AUDIT_AXIOM_COUNTS) != {path for path in paths if path.endswith("Audit.lean")}:
        raise ValueError("local immutable audit scope drift")
    result: dict[str, int] = {}
    for index, relative in enumerate(paths, start=1):
        if relative not in AUDIT_AXIOM_COUNTS:
            continue
        stem = Path(relative).stem
        suffix = re.sub(r"[^A-Za-z0-9]+", "_", stem).lower()
        result[f"p0_p9_{index:02d}_{suffix}"] = AUDIT_AXIOM_COUNTS[relative]
    if sum(result.values()) != EXPECTED_AXIOM_BLOCKS:
        raise ValueError("independent axiom-header total drift")
    return result


def stage_output(text: str, stage: str) -> str:
    command = f"STAGE={stage} CMD="
    result = f"STAGE={stage} EXIT="
    if text.count(command) != 1 or text.count(result) != 1:
        raise ValueError(f"stage delimiter count drift: {stage}")
    start = text.index("\n", text.index(command)) + 1
    end = text.index(result, start)
    return text[start:end]


def require_once(text: str, literal: str) -> None:
    count = text.count(literal)
    if count != 1:
        raise ValueError(f"marker count {count}, expected 1: {literal}")


def identify_supported_transcript(text: str) -> tuple[str, str, dict[str, str]]:
    matches: list[tuple[str, str, dict[str, str]]] = []
    for (source_sha, runner_rev), transport in SUPPORTED_TRANSCRIPTS.items():
        markers = (
            f"RUNNER_TRANSPORT_SHA256={transport['runner_sha256']}",
            f"P0_P9_MANIFEST_TRANSPORT_SHA256={transport['manifest_sha256']}",
            f"RUNNER_REV={runner_rev}",
            f"HEAD is now at {source_sha[:9]}",
        )
        if all(text.count(marker) == 1 for marker in markers):
            matches.append((source_sha, runner_rev, transport))
    if len(matches) != 1:
        raise ValueError(f"supported transcript identity count={len(matches)}")
    return matches[0]


def audit_p0(path: Path) -> str:
    """Audit the exact P0 pair even when a later stage stops the queue."""

    notebook_bytes = path.read_bytes()
    notebook = json.loads(notebook_bytes.decode("utf-8"))
    text, executed = output_text(notebook)
    if executed != 1:
        raise ValueError(f"executed code-cell count={executed}, expected 1")
    source_sha, runner_rev, transport = identify_supported_transcript(text)
    for literal in (
        f"RUNNER_TRANSPORT_SHA256={transport['runner_sha256']}",
        f"BASE_RUNNER_TRANSPORT_SHA256={BASE_RUNNER_SHA256}",
        f"P0_P9_PATHS_TRANSPORT_SHA256={PATHS_SHA256}",
        f"P0_P9_MANIFEST_TRANSPORT_SHA256={transport['manifest_sha256']}",
        f"RUNNER_REV={runner_rev}",
        f"HEAD is now at {source_sha[:9]}",
        "RUNTIME=CPU RAM_GIB=",
        f"LEAN_OVERLAY_TEXT_OK files={transport['overlay_files']}",
        f"LEAN_IMPORT_PREFIX_OK files={transport['overlay_files']}",
        "EVIDENCE_DOWNLOAD_REQUESTED=1",
        "LAUNCHER_RUNTIME_RELEASE_REQUESTED=1",
    ):
        require_once(text, literal)
    ram = re.search(r"RUNTIME=CPU RAM_GIB=([0-9]+(?:\.[0-9]+)?)", text)
    if ram is None or float(ram.group(1)) < 40:
        raise ValueError("high-RAM CPU runtime not proved")

    pass_count = text.count("FINAL_STATUS=PASS")
    fail_count = text.count("FINAL_STATUS=FAIL")
    if pass_count + fail_count != 1:
        raise ValueError("unique final status not proved")
    status = "PASS" if pass_count else "FAIL"
    require_once(text, "LAUNCHER_EXIT=0" if status == "PASS" else "LAUNCHER_EXIT=1")
    for forbidden in ("FORBIDDEN_AXIOM=", "sorryAx", "ofReduceBool"):
        if forbidden in text:
            raise ValueError(f"forbidden transcript marker: {forbidden}")

    stage_rows = re.findall(
        r"STAGE=([a-z0-9_]+) EXIT=([-0-9]+) SECONDS=([0-9]+(?:\.[0-9]+)?)",
        text,
    )
    order: list[str] = []
    stages: dict[str, int] = {}
    for stage, exit_code, _ in stage_rows:
        if stage in stages:
            raise ValueError(f"duplicate stage result: {stage}")
        order.append(stage)
        stages[stage] = int(exit_code)
    required_core = set(P0_REQUIRED_CORE_STAGES)
    if runner_rev != RUNNER_REV:
        # Historical transcripts predate the dedicated P3 dictionary repro.
        # They may certify the already-completed P0 prefix, but cannot be
        # required to contain a stage that did not yet exist in their runner.
        required_core.discard("p0_p9_p3_physical_dictionary_repro")
    missing_core = sorted(required_core - stages.keys())
    if missing_core:
        raise ValueError(f"missing prerequisite stage results: {missing_core}")
    for stage in (P0_SOURCE_STAGE, P0_AUDIT_STAGE):
        if stage not in stages or stages[stage] != 0:
            raise ValueError(f"required P0 stage not green: {stage}")
    if order.index(P0_SOURCE_STAGE) >= order.index(P0_AUDIT_STAGE):
        raise ValueError("P0 source/audit order drift")
    failed = [stage for stage in order if stages[stage] != 0]
    if status == "PASS" and failed:
        raise ValueError(f"PASS has nonzero stages: {failed}")
    if status == "FAIL" and (len(failed) != 1 or failed[0] != order[-1]):
        raise ValueError(f"stop-on-first-error not proved: {failed}")

    compact = re.sub(r"\s+", "", stage_output(text, P0_AUDIT_STAGE))
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != P0_AXIOM_HEADERS:
        raise ValueError(
            f"P0 axiom header count={len(blocks) + pure}, expected={P0_AXIOM_HEADERS}"
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise ValueError(f"forbidden P0 axiom block {index}: {sorted(names)}")

    evidence = re.findall(r"EVIDENCE_SHA256=([0-9a-f]{64})", text)
    archive = re.findall(r"EVIDENCE_ARCHIVE_SHA256=([0-9a-f]{64})", text)
    if len(evidence) != 1 or len(archive) != 1:
        raise ValueError("unique evidence hashes not proved")
    return (
        "P0_EXECUTED_NOTEBOOK_OK "
        f"source_sha={source_sha} runner_rev={runner_rev} status={status} "
        f"stages={len(stages)} p0_axiom_headers={P0_AXIOM_HEADERS} "
        f"evidence_sha256={evidence[0]} archive_sha256={archive[0]} "
        f"notebook_sha256={sha256(notebook_bytes)}"
    )


def audit_p1(path: Path) -> str:
    """Audit P0 and P1 even when a later stop-on-first-error ends the queue."""

    p0_result = audit_p0(path)
    notebook_bytes = path.read_bytes()
    notebook = json.loads(notebook_bytes.decode("utf-8"))
    text, executed = output_text(notebook)
    if executed != 1:
        raise ValueError(f"executed code-cell count={executed}, expected 1")
    source_stage = "p0_p9_03_p1coefficientmonotonicity"
    audit_stage = "p0_p9_04_p1coefficientmonotonicityaudit"
    stage_rows = re.findall(
        r"STAGE=([a-z0-9_]+) EXIT=([-0-9]+) SECONDS=([0-9]+(?:\.[0-9]+)?)",
        text,
    )
    order: list[str] = []
    stages: dict[str, int] = {}
    for stage, exit_code, _ in stage_rows:
        if stage in stages:
            raise ValueError(f"duplicate stage result: {stage}")
        order.append(stage)
        stages[stage] = int(exit_code)
    for stage in (source_stage, audit_stage):
        if stages.get(stage) != 0:
            raise ValueError(f"required P1 stage not green: {stage}")
    if order.index(source_stage) >= order.index(audit_stage):
        raise ValueError("P1 source/audit order drift")
    compact = re.sub(r"\s+", "", stage_output(text, audit_stage))
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != 8:
        raise ValueError(
            f"P1 axiom header count={len(blocks) + pure}, expected=8"
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise ValueError(f"forbidden P1 axiom block {index}: {sorted(names)}")
    return (
        "P1_EXECUTED_NOTEBOOK_OK "
        f"source_stage={source_stage} audit_stage={audit_stage} "
        f"axiom_headers={len(blocks) + pure} notebook_sha256={sha256(notebook_bytes)} "
        f"p0=({p0_result})"
    )


def audit(path: Path) -> str:
    notebook_bytes = path.read_bytes()
    notebook = json.loads(notebook_bytes.decode("utf-8"))
    text, executed = output_text(notebook)
    if executed != 1:
        raise ValueError(f"executed code-cell count={executed}, expected 1")

    transport = SUPPORTED_TRANSCRIPTS[(SOURCE_SHA, RUNNER_REV)]
    for literal in (
        f"RUNNER_TRANSPORT_SHA256={RUNNER_SHA256}",
        f"BASE_RUNNER_TRANSPORT_SHA256={BASE_RUNNER_SHA256}",
        f"P0_P9_PATHS_TRANSPORT_SHA256={PATHS_SHA256}",
        f"P0_P9_MANIFEST_TRANSPORT_SHA256={MANIFEST_SHA256}",
        f"RUNNER_REV={RUNNER_REV}",
        f"HEAD is now at {SOURCE_SHA[:9]}",
        "RUNTIME=CPU RAM_GIB=",
        f"LEAN_OVERLAY_TEXT_OK files={transport['overlay_files']}",
        f"LEAN_IMPORT_PREFIX_OK files={transport['overlay_files']}",
        "FINAL_STATUS=PASS",
        "EVIDENCE_DOWNLOAD_REQUESTED=1",
        "LAUNCHER_EXIT=0",
        "LAUNCHER_RUNTIME_RELEASE_REQUESTED=1",
    ):
        require_once(text, literal)

    ram = re.search(r"RUNTIME=CPU RAM_GIB=([0-9]+(?:\.[0-9]+)?)", text)
    if ram is None or float(ram.group(1)) < 40:
        raise ValueError("high-RAM CPU runtime not proved")
    for forbidden in (
        "FINAL_STATUS=FAIL",
        "FIRST_ERROR=",
        "FORBIDDEN_AXIOM=",
        "AXIOM_BLOCK_COUNT=",
        "sorryAx",
        "ofReduceBool",
    ):
        if forbidden in text:
            raise ValueError(f"forbidden transcript marker: {forbidden}")

    stage_rows = re.findall(
        r"STAGE=([a-z0-9_]+) EXIT=([-0-9]+) SECONDS=([0-9]+(?:\.[0-9]+)?)",
        text,
    )
    stages: dict[str, tuple[int, str]] = {}
    for stage, exit_code, seconds in stage_rows:
        if stage in stages:
            raise ValueError(f"duplicate stage result: {stage}")
        stages[stage] = (int(exit_code), seconds)
    expected = REQUIRED_CORE_STAGES | expected_queue_stages()
    missing = sorted(expected - stages.keys())
    if missing:
        raise ValueError(f"missing stage results: {missing}")
    failed = sorted(stage for stage, (code, _) in stages.items() if code != 0)
    if failed:
        raise ValueError(f"nonzero stage results: {failed}")

    axiom_headers = 0
    pure_headers = 0
    for stage, expected_headers in expected_audit_stages().items():
        compact = re.sub(r"\s+", "", stage_output(text, stage))
        blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
        pure = compact.count("doesnotdependonanyaxioms")
        if len(blocks) + pure != expected_headers:
            raise ValueError(
                f"axiom header count for {stage}={len(blocks) + pure}, "
                f"expected={expected_headers}, nonempty={len(blocks)}, empty={pure}"
            )
        for index, body in enumerate(blocks):
            names = {name for name in body.split(",") if name}
            if not names.issubset(ALLOWED_AXIOMS):
                raise ValueError(f"axiom block {stage}/{index}={sorted(names)}")
        axiom_headers += len(blocks) + pure
        pure_headers += pure

    evidence = re.findall(r"EVIDENCE_SHA256=([0-9a-f]{64})", text)
    archive = re.findall(r"EVIDENCE_ARCHIVE_SHA256=([0-9a-f]{64})", text)
    if len(evidence) != 1 or len(archive) != 1:
        raise ValueError("unique evidence hashes not proved")
    transcript_hash = sha256(text.encode("utf-8"))
    notebook_hash = sha256(notebook_bytes)
    return (
        "P0_P9_EXECUTED_NOTEBOOK_OK "
        f"source_sha={SOURCE_SHA} stages={len(stages)} queue_stages=39 "
        f"axiom_headers={axiom_headers} empty_axiom_headers={pure_headers} "
        f"evidence_sha256={evidence[0]} "
        f"archive_sha256={archive[0]} transcript_sha256={transcript_hash} "
        f"notebook_sha256={notebook_hash}"
    )


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: audit_p0_p9_executed_notebook.py EXECUTED.ipynb")
    try:
        print(audit(Path(sys.argv[1])))
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        print(f"P0_P9_EXECUTED_NOTEBOOK_FAIL {error}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
