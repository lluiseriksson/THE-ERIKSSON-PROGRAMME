#!/usr/bin/env python3
"""Warm, non-evidentiary continuation from a passed Eq359 Colab gate.

This script is intentionally diagnostic.  It reuses only the retained build
state of the exact Eq359 checkout, checks out the published Eq351 source
checkpoint, compiles the two Eq351 source/audit pairs, and then materializes
temporary public-import versions of the two regional-Laplacian drafts.  It
does not build terminal evidence, remove PRE-VALIDATION, commit, push, or
disconnect the runtime.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import time


ROOT = Path("/content/hrpoly-eq359-real-slice")
EVIDENCE = Path("/content/hrpoly-eq359-real-slice-evidence/evidence.json")
EQ359_SOURCE = "08039bcbc4bc74af072bef0252d7d559cbc80fe5"
EQ351_SOURCE = "0c88ed3c45626592367e2091a5f54c69cb624e3a"

EQ351_MODULES = (
    "BalabanCMP99ComplexSpecialLinearAdjointComposition",
    "BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization",
)

REGIONAL_DRAFTS = (
    (
        "tmp/BalabanCMP99Eq360ComplexRegionalLaplacian.draft.lean",
        "YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacian.lean",
        {
            "import tmp.BalabanCMP99ComplexSpecialLinearAdjointAction.draft":
                "import YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointAction",
        },
    ),
    (
        "tmp/BalabanCMP99Eq360ComplexRegionalLaplacianAudit.draft.lean",
        "YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianAudit.lean",
        {
            "import tmp.BalabanCMP99Eq360ComplexRegionalLaplacian.draft":
                "import YangMills.RG.BalabanCMP99Eq360ComplexRegionalLaplacian",
        },
    ),
    (
        "tmp/BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice.draft.lean",
        "YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice.lean",
        {
            "import tmp.BalabanCMP99Eq360ComplexRegionalLaplacian.draft":
                "import YangMills.RG.BalabanCMP99Eq360ComplexRegionalLaplacian",
            "import tmp.BalabanCMP99PhysicalBackgroundRealSlice.draft":
                "import YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice",
        },
    ),
    (
        "tmp/BalabanCMP99Eq360ComplexRegionalLaplacianRealSliceAudit.draft.lean",
        "YangMills/RG/BalabanCMP99Eq360ComplexRegionalLaplacianRealSliceAudit.lean",
        {
            "import tmp.BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice.draft":
                "import YangMills.RG.BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice",
        },
    ),
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run(stage: str, command: list[str]) -> str:
    started = time.perf_counter()
    print("WARM_STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    print(child.stdout, flush=True)
    print(
        f"WARM_STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}",
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("WARM_FIRST_ERROR=" + stage)
    return child.stdout


def require_passed_eq359() -> None:
    if not EVIDENCE.is_file():
        raise RuntimeError("WARM_EQ359_EVIDENCE_MISSING")
    evidence = json.loads(EVIDENCE.read_text(encoding="utf-8"))
    if evidence.get("status") != "PASS":
        raise RuntimeError("WARM_EQ359_NOT_PASS")
    if evidence.get("source_sha") != EQ359_SOURCE:
        raise RuntimeError("WARM_EQ359_SOURCE_MISMATCH")


def materialize_regional_drafts() -> None:
    for source_name, target_name, replacements in REGIONAL_DRAFTS:
        source = ROOT / source_name
        target = ROOT / target_name
        text = source.read_text(encoding="utf-8")
        for old, new in replacements.items():
            count = text.count(old)
            if count != 1:
                raise RuntimeError(
                    f"WARM_IMPORT_REPLACEMENT_COUNT={source_name}:{old}:{count}"
                )
            text = text.replace(old, new)
        target.write_text(text, encoding="utf-8", newline="\n")
        print(
            f"WARM_MATERIALIZED={target_name} SHA256={sha256(target).upper()}",
            flush=True,
        )


def compile_module(stage: str, module: str) -> None:
    source = f"YangMills/RG/{module}.lean"
    output = f".lake/build/lib/lean/YangMills/RG/{module}.olean"
    run(stage, ["lake", "env", "lean", source, "-o", output])


def main() -> int:
    require_passed_eq359()
    manifest_before = sha256(ROOT / "lake-manifest.json")
    toolchain_before = sha256(ROOT / "lean-toolchain")
    head = run("head_before", ["git", "rev-parse", "HEAD"]).strip()
    if head != EQ359_SOURCE:
        raise RuntimeError("WARM_HEAD_BEFORE_MISMATCH=" + head)

    run(
        "fetch_eq351",
        ["git", "fetch", "origin", EQ351_SOURCE],
    )
    run("checkout_eq351", ["git", "checkout", "--detach", EQ351_SOURCE])
    if sha256(ROOT / "lake-manifest.json") != manifest_before:
        raise RuntimeError("WARM_MANIFEST_DRIFT")
    if sha256(ROOT / "lean-toolchain") != toolchain_before:
        raise RuntimeError("WARM_TOOLCHAIN_DRIFT")

    run(
        "materialize_eq351_dependencies",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointAction",
            "YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice",
        ],
    )
    (ROOT / ".lake/build/lib/lean/YangMills/RG").mkdir(
        parents=True, exist_ok=True
    )
    for index, module in enumerate(EQ351_MODULES, start=1):
        compile_module(f"eq351_{index:02d}_{module.lower()}_source", module)
        compile_module(
            f"eq351_{index:02d}_{module.lower()}_audit", module + "Audit"
        )

    materialize_regional_drafts()
    for index, module in enumerate(
        (
            "BalabanCMP99Eq360ComplexRegionalLaplacian",
            "BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice",
        ),
        start=1,
    ):
        compile_module(f"regional_{index:02d}_{module.lower()}_source", module)
        compile_module(
            f"regional_{index:02d}_{module.lower()}_audit", module + "Audit"
        )

    print("WARM_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
