#!/usr/bin/env python3
"""Retained-runtime diagnostic for mixed and physical Eq. (2.46) aliasing.

This runner reuses only the already verified cold checkout and its build graph.
It fetches and hash-gates one immutable PRE-VALIDATION source checkpoint,
stops at the first real error, and retains the runtime.  Its output is hot
diagnostic evidence and cannot retire PRE-VALIDATION notices.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
import traceback
import urllib.request


HERE = Path("/content")
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bcc852cee5e709bff91fad7de26fa21cff754e1f/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)

with urllib.request.urlopen(BASE_RUNNER_URL, timeout=60) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location(
    "cmp99_full_point_source_mixed_domain_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


MIXED_DECLARATIONS = {
    "YangMills.RG.cmp99SourceFlatQprime_centered_eq_physical_or_add_period",
    "YangMills.RG.cmp89Eq249CentralEntireAveragePair_mixedCoarse_ne_zero",
    "YangMills.RG.cmp99SourceFlatFullPointSourceSolutionDomain_mixed",
    "YangMills.RG.cmp89Eq246PhysicalFineToFineGreenIntegrand_centered_eq_physical",
}

PHYSICAL_ALIAS_DECLARATIONS = {
    "YangMills.RG.cmp99Flat_normalizedFiniteGridFullPhysicalGreenSample_eq_residueClass",
}


def parse_axioms_exact(output: str, expected: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    without_axioms = re.findall(r"'([^']+)'doesnotdependonanyaxioms", compact)
    names = {name for name, _ in with_axioms} | set(without_axioms)
    if len(with_axioms) + len(without_axioms) != expected:
        raise RuntimeError(
            "AXIOM_BLOCK_COUNT_MISMATCH=" + repr((with_axioms, without_axioms))
        )
    expected_names = {
        4: MIXED_DECLARATIONS,
        1: PHYSICAL_ALIAS_DECLARATIONS,
    }.get(expected)
    if expected_names is None:
        raise RuntimeError("UNREGISTERED_AXIOM_BLOCK_COUNT=" + str(expected))
    if names != expected_names:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    for name, raw_axioms in with_axioms:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)
    for name in without_axioms:
        print("AXIOM_GATE=" + name + " AXIOMS=", flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp99-full-point-source-mixed-domain-retained-hot-v2"
runner.SOURCE_SHA = "f9f3b385cd84eb5820d628481bc86d2e48cc216a"
runner.ROOT = Path(
    "/content/hrpoly-cmp99-full-point-source-solution-domain-cold-v1"
)
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-full-point-source-mixed-domain-retained-hot-v2-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-full-point-source-mixed-domain-retained-hot-v2-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-full-point-source-mixed-domain-retained-hot-v2-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceMixedDomain.lean":
        "faef89f4e34061de0111c3cca4f82859569fdcee984a67be1596c3eaabcbaf26",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceMixedDomainAudit.lean":
        "fe0a22fe2d046fbc1b105a32bcf2c687e7c40e63f55b46b56a47aa7df19aec38",
    "YangMills/RG/BalabanCMP99FullGreenPhysicalFiniteGridAliasing.lean":
        "a7b745946fc3f72f8ea58e0983dc884e41084568f423288c88dbb4ece10a7b85",
    "YangMills/RG/BalabanCMP99FullGreenPhysicalFiniteGridAliasingAudit.lean":
        "ae2f0ed9096cd50f5db0833b741a35c4e6263b9f0183eb3129255f16cbc48112",
}
runner.QUEUE = [
    (
        "full_point_source_mixed_domain_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceMixedDomain",
        ],
        None,
    ),
    (
        "full_point_source_mixed_domain_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceMixedDomainAudit.lean",
        ],
        4,
    ),
    (
        "full_physical_finite_grid_aliasing_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99FullGreenPhysicalFiniteGridAliasing",
        ],
        None,
    ),
    (
        "full_physical_finite_grid_aliasing_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99FullGreenPhysicalFiniteGridAliasingAudit.lean",
        ],
        1,
    ),
]


def retained_main() -> int:
    opened = runner.utc_now()
    status = "FAIL"
    print("RUNNER_REV=" + runner.RUNNER_REV, flush=True)
    print("HOT_DEBUG_NOT_EVIDENCE=1", flush=True)
    print("STAGE=runtime_reuse UTC=" + opened, flush=True)
    try:
        if not runner.ROOT.is_dir():
            raise RuntimeError("RETAINED_ROOT_MISSING=" + str(runner.ROOT))
        runner.RECORDS.clear()
        old_head = runner.run(
            "retained_head_before", ["git", "rev-parse", "HEAD"], cwd=runner.ROOT
        ).strip()
        print("RETAINED_HEAD_BEFORE=" + old_head, flush=True)
        runner.run(
            "fetch_source",
            ["git", "fetch", "--no-tags", "origin", runner.SOURCE_SHA],
            cwd=runner.ROOT,
        )
        runner.run(
            "checkout_source",
            ["git", "checkout", "--detach", runner.SOURCE_SHA],
            cwd=runner.ROOT,
        )
        head = runner.run(
            "retained_head_after", ["git", "rev-parse", "HEAD"], cwd=runner.ROOT
        ).strip()
        if head != runner.SOURCE_SHA:
            raise RuntimeError("SOURCE_SHA_MISMATCH=" + head)
        runner.verify_source_blobs()
        runner.PATH_MANIFEST.write_text(
            "\n".join(runner.SOURCE_BLOBS) + "\n", encoding="utf-8"
        )
        runner.run(
            "overlay_text_guard",
            [
                "python3", "scripts/check_lean_overlay_text.py",
                "--paths-from", str(runner.PATH_MANIFEST),
            ],
            cwd=runner.ROOT,
        )
        runner.run(
            "import_prefix_guard",
            [
                "python3", "scripts/check_lean_import_prefix.py",
                *runner.SOURCE_BLOBS.keys(),
            ],
            cwd=runner.ROOT,
        )
        for stage, command, expected_axioms in runner.QUEUE:
            output = runner.run(stage, command, cwd=runner.ROOT)
            if expected_axioms is not None:
                runner.parse_axioms(output, expected_axioms)
        status = "PASS"
    except Exception as error:
        print("ERROR=" + repr(error), flush=True)
        traceback.print_exc()
    finally:
        evidence_hash, archive_hash = runner.make_evidence(status, opened)
        print("EVIDENCE_SHA256=" + evidence_hash, flush=True)
        print("EVIDENCE_ARCHIVE=" + str(runner.ARCHIVE), flush=True)
        print("EVIDENCE_ARCHIVE_SHA256=" + archive_hash, flush=True)
        print("FINAL_STATUS=" + status, flush=True)
        print("RUNTIME_RETAINED_FOR_DEBUG=1", flush=True)
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(retained_main())
