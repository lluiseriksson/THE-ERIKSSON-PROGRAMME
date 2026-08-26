#!/usr/bin/env python3
"""Resume the bounded Eq351 warm diagnostic at its first failed target.

Run only in the retained runtime of the Eq359 cold PASS after the first
positive-adjoint postpass stopped at the regional Laplacian source.  The
script verifies that exact retained state, fetches the one-line geometry
repair, and resumes at the failed target.  It neither reruns the Eq359 cold
gate nor releases the runtime, removes PRE-VALIDATION, commits, or pushes.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import time


ROOT = Path("/content/hrpoly-eq359-real-slice")
EVIDENCE = Path("/content/hrpoly-eq359-real-slice-evidence/evidence.json")
EQ359_SOURCE = "cd6ff65638f0e09e2533733df2d7176c10714a3a"
EXPECTED_HEAD_BEFORE = "127aa09344ebf95dc3673371c85d0752593b28bc"
FIX_SOURCE = "f8862ca3f320cdd0d193192f022135566618886b"

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

EXPANSION_DRAFTS = (
    (
        "tmp/BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion.draft.lean",
        "YangMills/RG/BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion.lean",
        {},
    ),
    (
        "tmp/BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansionAudit.draft.lean",
        "YangMills/RG/BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansionAudit.lean",
        {
            "import tmp.BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion.draft":
                "import YangMills.RG.BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion",
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
    print("RETRY_STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
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
        f"RETRY_STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}",
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("RETRY_FIRST_ERROR=" + stage)
    return child.stdout


def require_eq359_pass() -> None:
    if not EVIDENCE.is_file():
        raise RuntimeError("RETRY_EQ359_EVIDENCE_MISSING")
    evidence = json.loads(EVIDENCE.read_text(encoding="utf-8"))
    if evidence.get("status") != "PASS":
        raise RuntimeError("RETRY_EQ359_NOT_PASS")
    if evidence.get("source_sha") != EQ359_SOURCE:
        raise RuntimeError("RETRY_EQ359_SOURCE_MISMATCH")


def materialize(rows: tuple[tuple[str, str, dict[str, str]], ...]) -> None:
    for source_name, target_name, replacements in rows:
        source = ROOT / source_name
        target = ROOT / target_name
        text = source.read_text(encoding="utf-8")
        for old, new in replacements.items():
            count = text.count(old)
            if count != 1:
                raise RuntimeError(
                    f"RETRY_IMPORT_REPLACEMENT_COUNT={source_name}:{old}:{count}"
                )
            text = text.replace(old, new)
        if "import tmp." in text:
            raise RuntimeError("RETRY_TMP_IMPORT_REMAINS=" + source_name)
        target.write_text(text, encoding="utf-8", newline="\n")
        print(
            f"RETRY_MATERIALIZED={target_name} SHA256={sha256(target).upper()}",
            flush=True,
        )


def compile_module(stage: str, module: str) -> None:
    source = f"YangMills/RG/{module}.lean"
    output = f".lake/build/lib/lean/YangMills/RG/{module}.olean"
    run(stage, ["lake", "env", "lean", source, "-o", output])


def main() -> int:
    require_eq359_pass()
    manifest_before = sha256(ROOT / "lake-manifest.json")
    toolchain_before = sha256(ROOT / "lean-toolchain")
    head = run("head_before", ["git", "rev-parse", "HEAD"]).strip()
    if head != EXPECTED_HEAD_BEFORE:
        raise RuntimeError("RETRY_HEAD_BEFORE_MISMATCH=" + head)

    run("fetch_fix", ["git", "fetch", "origin", FIX_SOURCE])
    run("checkout_fix", ["git", "checkout", "--detach", FIX_SOURCE])
    if sha256(ROOT / "lake-manifest.json") != manifest_before:
        raise RuntimeError("RETRY_MANIFEST_DRIFT")
    if sha256(ROOT / "lean-toolchain") != toolchain_before:
        raise RuntimeError("RETRY_TOOLCHAIN_DRIFT")

    materialize(REGIONAL_DRAFTS)
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

    for index, module in enumerate(
        (
            "BalabanCMP99ComplexSpecialLinearAdjointComposition",
            "BalabanCMP99Eq351PhysicalComplexPositiveBondFactorization",
        ),
        start=1,
    ):
        compile_module(f"eq351_{index:02d}_{module.lower()}_source", module)
        compile_module(
            f"eq351_{index:02d}_{module.lower()}_audit", module + "Audit"
        )

    materialize(EXPANSION_DRAFTS)
    module = "BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion"
    compile_module("eq351_positive_adjoint_expansion_source", module)
    compile_module("eq351_positive_adjoint_expansion_audit", module + "Audit")

    print("WARM_POSITIVE_ADJOINT_RETRY_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except BaseException as exc:
        print("WARM_POSITIVE_ADJOINT_RETRY_FINAL_STATUS=FAIL", flush=True)
        print("WARM_POSITIVE_ADJOINT_RETRY_ERROR=" + repr(exc), flush=True)
        raise
