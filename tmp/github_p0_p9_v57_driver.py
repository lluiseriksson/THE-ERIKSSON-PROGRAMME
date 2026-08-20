#!/usr/bin/env python3
"""Exact stop-on-first-error GitHub driver for the P0--P9 v57 scratch chain."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


SOURCE_SHA = "ff9fcb0ef8cadeef13fb4213f38f914bbd951150"
PATHS_SHA256 = "fec594c0fba52e14f8cc1e1ba886202fcdf2e425de2c93e56dbf59feebb2fa61"
MANIFEST_SHA256 = "dc84c75c8e6d2428869ac0b95b88e614e88b376f723700ea9e1c09a38a202381"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REPROS = {
    "tmp/P2bEffectiveQuadraticAlgebra.repro.lean": "eb383078580605d6d3be28700c6c65e6de8738cc969b5e5269de9fb4982dcf7c",
    "tmp/P3BlockGaussianAlgebra.repro.lean": "520bbeca32622084706e4aee6b35adaea1b4f0c3f40077da9fbca4a9ad4bd38a",
    "tmp/P3TypedSchurAveraging.repro.lean": "14efa63ece428de46e183edef7e3224053f8eba1e4630e041833f754954dc6a6",
    "tmp/P3TypedGreenInverseAlgebra.repro.lean": "dbdab8f3c5b0e2ae20c98568a3d114195aad1989283d4715f237edb3adb12137",
    "tmp/P3PhysicalOperatorDictionaryComposition.repro.lean": "74f1a221b8097016397c15eb10dfbe5b8535ab096380499f160b55781164fda8",
}
AXIOM_COUNTS = {
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
    "tmp/P5PhysicalGreenScaleDictionaryAudit.lean": 13,
    "tmp/P7SourceSeparatedAmbientPrefixPrecisionAudit.lean": 8,
    "tmp/P8SourceSeparatedRegionalPrefixGreenAudit.lean": 5,
    "tmp/P9SourceSeparatedPrefixCombesThomasAudit.lean": 12,
}
P0_P5_PREREQUISITES = (
    "YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge",
    "YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance",
    "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.FinitePiLpTypedKernelReindexAlgebra",
)
P7_P9_PREREQUISITES = (
    "YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.BalabanCMP99SourceGeneratedRegionalFinePartition",
    "YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition",
    "YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas",
    "YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stage_for(index: int, path: str) -> str:
    return (
        f"p0_p9_{index:02d}_"
        + re.sub(r"[^A-Za-z0-9]+", "_", Path(path).stem).lower()
    )


def parse_axioms(output: str, expected: int) -> list[list[str]]:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise ValueError(f"forbidden axiom marker: {forbidden}")
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != expected:
        raise ValueError(
            f"axiom header count={len(blocks) + pure}, expected={expected}"
        )
    parsed: list[list[str]] = []
    for body in blocks:
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise ValueError(f"forbidden axiom set: {sorted(names)}")
        parsed.append(sorted(names))
    parsed.extend([] for _ in range(pure))
    return parsed


def exact_paths(repo: Path) -> list[str]:
    paths_file = repo / "tmp/P0-P9-SCRATCH-PATHS.txt"
    manifest_file = repo / "tmp/P0-P9-SCRATCH-MANIFEST.sha256"
    if sha256(paths_file.read_bytes()) != PATHS_SHA256:
        raise ValueError("path-list digest drift")
    if sha256(manifest_file.read_bytes()) != MANIFEST_SHA256:
        raise ValueError("manifest digest drift")
    paths = [
        line for line in paths_file.read_text(encoding="utf-8-sig").splitlines()
        if line
    ]
    rows = []
    for line in manifest_file.read_text(encoding="utf-8-sig").splitlines():
        digest, path = line.split(None, 1)
        rows.append((path.strip(), digest.lower()))
    if len(paths) != 39 or [path for path, _ in rows] != paths:
        raise ValueError("path/manifest scope drift")
    for path, expected in rows:
        if sha256((repo / path).read_bytes()) != expected:
            raise ValueError(f"source blob drift: {path}")
    for path, expected in REPROS.items():
        if sha256((repo / path).read_bytes()) != expected:
            raise ValueError(f"repro blob drift: {path}")
    if set(AXIOM_COUNTS) != {path for path in paths if path.endswith("Audit.lean")}:
        raise ValueError("axiom audit scope drift")
    return paths


def queue(paths: list[str]) -> list[tuple[str, list[str], int | None]]:
    result: list[tuple[str, list[str], int | None]] = [
        (
            "p0_p9_static_gate",
            ["python3", "tmp/audit_p0_p9_diagnostic.py"], None,
        ),
        (
            "p0_p9_static_selftest",
            ["python3", "tmp/test_p0_p9_diagnostic.py"], None,
        ),
    ]
    repro_stems = (
        ("p0_p9_p2b_algebra_repro", "tmp/P2bEffectiveQuadraticAlgebra.repro.lean"),
        ("p0_p9_p3_algebra_repro", "tmp/P3BlockGaussianAlgebra.repro.lean"),
        ("p0_p9_p3_typed_averaging_repro", "tmp/P3TypedSchurAveraging.repro.lean"),
        ("p0_p9_p3_typed_green_inverse_repro", "tmp/P3TypedGreenInverseAlgebra.repro.lean"),
        ("p0_p9_p3_physical_dictionary_repro", "tmp/P3PhysicalOperatorDictionaryComposition.repro.lean"),
    )
    result.extend((stage, ["lake", "env", "lean", path], None) for stage, path in repro_stems)
    result.extend(
        [
            (
                "p0_p9_materialize_project_prerequisites",
                ["lake", "build", *P0_P5_PREREQUISITES], None,
            ),
            (
                "p0_p9_prepare_scratch_build_dir",
                ["mkdir", "-p", ".lake/build/lib/lean/tmp"], None,
            ),
        ]
    )
    for index, path in enumerate(paths, start=1):
        if path == "tmp/P7SourceSeparatedAmbientPrefixPrecision.lean":
            result.append(
                (
                    "p0_p9_materialize_p7_p9_project_prerequisites",
                    ["lake", "build", *P7_P9_PREREQUISITES], None,
                )
            )
        command = ["lake", "env", "lean", path]
        if path not in AXIOM_COUNTS:
            command.extend(["-o", f".lake/build/lib/lean/{Path(path).with_suffix('.olean').as_posix()}"])
        result.append((stage_for(index, path), command, AXIOM_COUNTS.get(path)))
    return result


def run_stage(
    repo: Path, evidence: Path, stage: str, command: list[str]
) -> tuple[dict[str, object], str]:
    started = time.perf_counter()
    child = subprocess.run(
        command, cwd=repo, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False
    )
    elapsed = time.perf_counter() - started
    output = child.stdout
    print(f"STAGE={stage} CMD={json.dumps(command)}", flush=True)
    print(output, flush=True)
    log_name = f"{stage}.log"
    (evidence / log_name).write_text(output, encoding="utf-8", newline="\n")
    record = {
        "stage": stage,
        "exit": child.returncode,
        "seconds": elapsed,
        "log": log_name,
        "output_sha256": sha256(output.encode()),
    }
    print(f"STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}", flush=True)
    return record, output


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path)
    parser.add_argument("--evidence", type=Path)
    parser.add_argument("--contract-only", action="store_true")
    args = parser.parse_args()
    if args.contract_only:
        paths = exact_paths(Path(__file__).resolve().parents[1])
        stages = queue(paths)
        if len(stages) != 49 or sum(AXIOM_COUNTS.values()) != 199:
            raise SystemExit("P0_P9_V57_GITHUB_CONTRACT_DRIFT")
        print(
            "P0_P9_V57_GITHUB_CONTRACT_OK paths=39 stages=49 "
            "audits=20 axiom_headers=199"
        )
        return 0
    if args.repo is None or args.evidence is None:
        raise SystemExit("--repo and --evidence are required")
    repo = args.repo.resolve()
    evidence = args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    records: list[dict[str, object]] = []
    axioms: dict[str, list[list[str]]] = {}
    status = "FAIL"
    first_error: str | None = None
    try:
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=repo, text=True,
            stdout=subprocess.PIPE, check=True
        ).stdout.strip()
        if head != SOURCE_SHA:
            raise ValueError(f"source checkpoint mismatch: {head}")
        paths = exact_paths(repo)
        for stage, command, expected_axioms in queue(paths):
            record, output = run_stage(repo, evidence, stage, command)
            records.append(record)
            if record["exit"] != 0:
                first_error = stage
                raise RuntimeError(f"FIRST_ERROR={stage}")
            if expected_axioms is not None:
                axioms[stage] = parse_axioms(output, expected_axioms)
        if sum(len(value) for value in axioms.values()) != 199:
            raise ValueError("total axiom header drift")
        status = "PASS"
        return 0
    except Exception as error:
        if first_error is None:
            first_error = type(error).__name__
        print(f"ERROR={error!r}", flush=True)
        return 1
    finally:
        summary = {
            "source_sha": SOURCE_SHA,
            "mathlib_sha": MATHLIB_SHA,
            "status": status,
            "first_error": first_error,
            "records": records,
            "axiom_headers": sum(len(value) for value in axioms.values()),
        }
        (evidence / "evidence.json").write_text(
            json.dumps(summary, sort_keys=True, indent=2) + "\n", encoding="utf-8"
        )
        (evidence / "axioms.json").write_text(
            json.dumps(axioms, sort_keys=True, indent=2) + "\n", encoding="utf-8"
        )
        (evidence / "FINAL_STATUS").write_text(
            f"FINAL_STATUS={status}\n", encoding="utf-8"
        )
        print(f"FINAL_STATUS={status}", flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
