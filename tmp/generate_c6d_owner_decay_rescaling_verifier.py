#!/usr/bin/env python3
"""Generate the fail-closed verifier for C6d owner-distance rescaling."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "generate_finite_pilp_distance_rescaling_verifier.py"
DEFAULT_RUNNER = ROOT / "scripts" / "colab_c6d_owner_decay_rescaling_validation.py"
DEFAULT_NOTEBOOK = ROOT / "scripts" / "colab_c6d_owner_decay_rescaling_validation.ipynb"
DEFAULT_OUTPUT = ROOT / "tmp" / "verify_c6d_owner_decay_rescaling_evidence.py"


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_owner_rescaling_verifier_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_OWNER_RESCALING_VERIFIER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def generated_text(source_sha: str, runner: Path, notebook: Path) -> str:
    base = load_base()
    content = base.generated_text(source_sha, runner, notebook)
    replacements = (
        (
            "kernel-distance rescaling",
            "C6d owner-distance rescaling",
        ),
        (
            'SUCCESS_SENTINEL = "DISTANCE_RESCALING_EVIDENCE_OK"',
            'SUCCESS_SENTINEL = "C6D_OWNER_RESCALING_EVIDENCE_OK"',
        ),
        (
            'MODULES = ["FinitePiLpTypedKernelDistanceRescaling"]',
            'MODULES = ["BalabanCMP99Eq360C6dSourceSeparatedOwnerDecayRescaling"]',
        ),
        (
            '"01_finitepilptypedkerneldistancerescaling_audit"',
            '"01_balabancmp99eq360c6dsourceseparatedownerdecayrescaling_audit"',
        ),
        (
            '"01_finitepilptypedkerneldistancerescaling_focal"',
            '"01_balabancmp99eq360c6dsourceseparatedownerdecayrescaling_focal"',
        ),
        (
            '"02_finite_pilp_distance_rescaling_yang_mills_core_root"',
            '"02_c6d_owner_decay_rescaling_yang_mills_core_root"',
        ),
        (
            '"distance_rescaling_evidence_base"',
            '"c6d_owner_rescaling_evidence_base"',
        ),
    )
    for old, new in replacements:
        if old not in content:
            raise RuntimeError("C6D_OWNER_RESCALING_VERIFIER_REPLACEMENT_MISSING")
        content = content.replace(old, new)
    return content


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner", type=Path, default=DEFAULT_RUNNER)
    parser.add_argument("--notebook", type=Path, default=DEFAULT_NOTEBOOK)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    content = generated_text(args.source_sha, args.runner.resolve(), args.notebook.resolve())
    compile(content, str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "C6D_OWNER_RESCALING_VERIFIER_GENERATED "
        f"source_sha={args.source_sha} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
