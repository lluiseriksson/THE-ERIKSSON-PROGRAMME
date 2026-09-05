#!/usr/bin/env python3
"""Retained-runtime diagnostic for full endpoint reflection and owner orientation.

This hot runner reuses the exact fresh graph retained by the preceding cold
orientation seal.  It hash-gates the promoted PRE-VALIDATION checkpoint and
stops at the first focal or axiom error.  A PASS is diagnostic only and cannot
retire PRE-VALIDATION notices.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


HERE = Path("/content")
BASE = HERE / "colab_cmp99_full_point_source_orientation_hot_v7.py"
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "61e6e1c3c9c0d2ee9a0451ff5fafc880522607bd/"
    "scripts/colab_cmp99_full_point_source_mixed_domain_retained_hot.py"
)
BASE_SHA256 = (
    "cac78a2294d410915023ef7942de1e98f89955ebab462626106ac558c1aa3042"
)

with urllib.request.urlopen(BASE_URL, timeout=60) as response:
    source = response.read()
digest = hashlib.sha256(source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + digest, flush=True)
if digest != BASE_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE.write_bytes(source)

spec = importlib.util.spec_from_file_location("cmp99_endpoint_reflection_base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load retained base: {BASE}")
hot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(hot)
runner = hot.runner

# `Matrix.ToLin` exposes the complex type but not its algebra instances in the
# pinned Mathlib graph.  Keep the inherited repro, but make its standalone
# import boundary explicit before any project focal is attempted.
hot.TRANSPOSE_PAIRING_REPRO = (
    "import Mathlib.Data.Complex.Basic\n" + hot.TRANSPOSE_PAIRING_REPRO
)

runner.RUNNER_REV = "cmp99-full-endpoint-reflection-retained-hot-v1"
runner.SOURCE_SHA = "5e515584cf1975c947424945bc8cc587192bcf57"
runner.ROOT = Path("/content/hrpoly-cmp99-full-point-source-orientation-cold-v3")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-full-endpoint-reflection-retained-hot-v1-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-full-endpoint-reflection-retained-hot-v1-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-full-endpoint-reflection-retained-hot-v1-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceOuterSynthesisDictionary.lean":
        "6a35a5ce08b9fa3e64e9da864b620f4221cadbfcef53727b475b998340884f7a",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceOuterSynthesisDictionaryAudit.lean":
        "a7a4c2ca1b08c532d79d33e3a6cf7c1c32396cbd52f22432f1a65b9ca398cc28",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOwnerCharacter.lean":
        "be3196371c0e0b6a2e8beec1dce01fa8a4a46d012885674c77d0cecddfe377ac",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOwnerCharacterAudit.lean":
        "4c6307faaba172f3ab58b05e2dcea8b64f540e60fcb126ec7a6c07287d59099c",
    "YangMills/RG/BalabanCMP89Eq246FullEndpointReflection.lean":
        "d0ab03f497690c2370d4920c854a075fa46ae66333b2e4800a5ff40d59591438",
    "YangMills/RG/BalabanCMP89Eq246FullEndpointReflectionAudit.lean":
        "5fe7022af3af5212ad1dcb4ddff575c47a74ac03aa4aa4160021515a240c717a",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceReversedOwnerCharacter.lean":
        "4f02691e159071afc337350a991d38dfbd6cb58af16f0206a51e2820a58f5254",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceReversedOwnerCharacterAudit.lean":
        "2607548979e0b2d7f7fc236abe3cf43712f22c1812c8111cd8e07b9bcb7bb586",
}

runner.QUEUE = [
    (
        "generated_outer_synthesis_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPointSourceOuterSynthesisDictionary"],
        None,
    ),
    (
        "generated_outer_synthesis_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceOuterSynthesisDictionaryAudit.lean"],
        frozenset({
            "YangMills.RG.cmp99SourceGeneratedFlatPhysicalPointSourceGreen_apply_eq_outerIntegrandSum",
        }),
    ),
    (
        "owner_character_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceOwnerCharacter"],
        None,
    ),
    (
        "owner_character_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOwnerCharacterAudit.lean"],
        frozenset({
            "YangMills.RG.cmp99FlatFourierMode_target_mul_source_inv_eq_ownerDifferenceCharacter",
        }),
    ),
    (
        "full_endpoint_reflection_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246FullEndpointReflection"],
        None,
    ),
    (
        "full_endpoint_reflection_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246FullEndpointReflectionAudit.lean"],
        frozenset({
            "YangMills.RG.cmp89Eq246StabilizedDepthOnePhysicalEndpointReflection",
            "YangMills.RG.cmp89Eq246PhysicalFineToFineGreenIntegrand_neg_swap",
        }),
    ),
    (
        "reversed_owner_character_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceReversedOwnerCharacter"],
        None,
    ),
    (
        "reversed_owner_character_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceReversedOwnerCharacterAudit.lean"],
        frozenset({
            "YangMills.RG.cmp99FlatFourierMode_target_mul_source_inv_eq_reversedOwnerDifferenceCharacter",
        }),
    ),
]


if __name__ == "__main__":
    raise SystemExit(hot.retained_main())
