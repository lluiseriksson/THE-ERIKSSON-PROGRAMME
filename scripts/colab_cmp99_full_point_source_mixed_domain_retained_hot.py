#!/usr/bin/env python3
"""Retained-runtime diagnostic for mixed/physical Eq. (2.46) orientation.

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

TRANSPOSE_PAIRING_DECLARATIONS = {
    "YangMills.RG.cmp89Eq246StabilizedAliasFullSolution_transpose_pairing",
}

REFLECTION_INVOLUTION_DECLARATIONS = {
    "YangMills.RG.cmp99SourceCenteredAliasReflection_apply_apply",
    "YangMills.RG.cmp99SourceCenteredAliasVectorReflection_apply_apply",
    "YangMills.RG.cmp99SourceAliasIndexOneReflection_apply_apply",
}

TARGET_DUALITY_DECLARATIONS = {
    "YangMills.RG.cmp89Eq246FinePointSourceAliasVector_negEndpoint_eq_targetPhase",
    "YangMills.RG.cmp89Eq246FinePointSourceAliasVector_negPhysicalEndpoint_eq_targetPhase",
}

TRANSPOSE_PAIRING_REPRO = r'''import Mathlib.LinearAlgebra.Matrix.ToLin

open Matrix

example {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (x y source target : ι → ℂ)
    (hx : A.mulVec x = source)
    (hy : A.transpose.mulVec y = target) :
    dotProduct target x = dotProduct source y := by
  classical
  calc
    dotProduct target x = dotProduct (A.transpose.mulVec y) x := by rw [hy]
    _ = dotProduct x (A.transpose.mulVec y) := dotProduct_comm _ _
    _ = dotProduct (A.mulVec x) y := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = dotProduct y (A.mulVec x) := dotProduct_comm _ _
    _ = dotProduct y source := by rw [hx]
    _ = dotProduct source y := dotProduct_comm _ _
'''


def parse_axioms_exact(output: str, expected: frozenset[str]) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    without_axioms = re.findall(r"'([^']+)'doesnotdependonanyaxioms", compact)
    names = {name for name, _ in with_axioms} | set(without_axioms)
    if len(with_axioms) + len(without_axioms) != len(expected):
        raise RuntimeError(
            "AXIOM_BLOCK_COUNT_MISMATCH=" + repr((with_axioms, without_axioms))
        )
    if names != expected:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    for name, raw_axioms in with_axioms:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)
    for name in without_axioms:
        print("AXIOM_GATE=" + name + " AXIOMS=", flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp99-full-point-source-mixed-domain-retained-hot-v7"
runner.SOURCE_SHA = "6d847ab0e386b091e8ab9843d615c39bd3b41939"
runner.ROOT = Path(
    "/content/hrpoly-cmp99-full-point-source-solution-domain-cold-v1"
)
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-full-point-source-mixed-domain-retained-hot-v6-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-full-point-source-mixed-domain-retained-hot-v6-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-full-point-source-mixed-domain-retained-hot-v6-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceMixedDomain.lean":
        "38072a32c67ab366e5754382e2568a60b6a3c24ab2ebebc33641abd31eb0fd82",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceMixedDomainAudit.lean":
        "572e7657ca326375a4f082ae7be0492db7dec8b84a80357a71d7a0abfab45c41",
    "YangMills/RG/BalabanCMP99FullGreenPhysicalFiniteGridAliasing.lean":
        "9e8cdbfb4c5f56ce0b66f8b48035bfcc8bb3f5516ca4044ca670d352942c3825",
    "YangMills/RG/BalabanCMP99FullGreenPhysicalFiniteGridAliasingAudit.lean":
        "1ea4a05cbf74806be1cf6da268e148a595bf33aa25e466e3aad94a0d865aa629",
    "YangMills/RG/BalabanCMP89Eq246StabilizedAliasFullTransposePairing.lean":
        "073d5af16e7ce73cd2fe657be5ad7dc0d264a0abc5966dd311a4dd9aa3aa3fd1",
    "YangMills/RG/BalabanCMP89Eq246StabilizedAliasFullTransposePairingAudit.lean":
        "d4eb6582ed6b91af3a8f23420ae5a8c8308d3010fb81eedc6486cd4b0fe2b101",
    "YangMills/RG/BalabanCMP99SourceAliasReflectionInvolutive.lean":
        "583c12919bece2337b9e4b0d1e2a9887e4c4724e7f2f1af34705c08b10bf374a",
    "YangMills/RG/BalabanCMP99SourceAliasReflectionInvolutiveAudit.lean":
        "bba1fe8f1349a2217f83fbd87139aa1996fed2973ca46c9d33ff61be291011ec",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceTargetDuality.lean":
        "b27f0d52f0aee0f34d4ece07c2887c96c07695374b33051e399604b2903dcd3c",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceTargetDualityAudit.lean":
        "1189fb9642da9c352d1dd1469205ec2f59c96495166869e53478a0213d32a1c9",
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
        frozenset(MIXED_DECLARATIONS),
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
        frozenset(PHYSICAL_ALIAS_DECLARATIONS),
    ),
    (
        "full_direct_transpose_pairing_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP89Eq246StabilizedAliasFullTransposePairing",
        ],
        None,
    ),
    (
        "full_direct_transpose_pairing_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP89Eq246StabilizedAliasFullTransposePairingAudit.lean",
        ],
        frozenset(TRANSPOSE_PAIRING_DECLARATIONS),
    ),
    (
        "alias_reflection_involution_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceAliasReflectionInvolutive",
        ],
        None,
    ),
    (
        "alias_reflection_involution_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceAliasReflectionInvolutiveAudit.lean",
        ],
        frozenset(REFLECTION_INVOLUTION_DECLARATIONS),
    ),
    (
        "fine_point_source_target_duality_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP89Eq246FinePointSourceTargetDuality",
        ],
        None,
    ),
    (
        "fine_point_source_target_duality_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP89Eq246FinePointSourceTargetDualityAudit.lean",
        ],
        frozenset(TARGET_DUALITY_DECLARATIONS),
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
        repro = runner.ROOT / "tmp" / "CMP89FullTransposePairingRepro.lean"
        repro.parent.mkdir(parents=True, exist_ok=True)
        repro.write_text(TRANSPOSE_PAIRING_REPRO, encoding="utf-8")
        runner.run(
            "full_transpose_pairing_mathlib_repro",
            ["lake", "env", "lean", str(repro.relative_to(runner.ROOT))],
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
