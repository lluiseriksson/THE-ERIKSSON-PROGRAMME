#!/usr/bin/env python3
"""Fresh-checkout cold gate for the complete endpoint-reflection prefix.

Promote this wrapper only after all three retained-runtime queues pass.  It
checks the exact twelve-file chain at one immutable source checkpoint without
restoring a project build graph.  The runtime is retained only for one
bounded first-error repair.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


HERE = Path("/content")
HOT_RUNNER = HERE / "colab_cmp99_physical_endpoint_reflection_retained_hot_v2.py"
HOT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "51bd275d/"
    "scripts/colab_cmp99_physical_endpoint_reflection_retained_hot.py"
)
HOT_RUNNER_SHA256 = (
    "dbda26442f2aa4f07cf1c4a2ec30576e728837d2dff6330e7549e5d8269880d0"
)

with urllib.request.urlopen(HOT_RUNNER_URL, timeout=60) as response:
    hot_runner_source = response.read()
hot_runner_hash = hashlib.sha256(hot_runner_source).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + hot_runner_hash, flush=True)
if hot_runner_hash != HOT_RUNNER_SHA256:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
HOT_RUNNER.write_bytes(hot_runner_source)

spec = importlib.util.spec_from_file_location(
    "cmp99_physical_endpoint_reflection_retained_hot_v2", HOT_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load hot runner: {HOT_RUNNER}")
physical = importlib.util.module_from_spec(spec)
spec.loader.exec_module(physical)
runner = physical.runner

runner.RUNNER_REV = "cmp99-endpoint-reflection-chain-cold-v2"
runner.SOURCE_SHA = "4d61fbd43d48887da9009ba92941b83673acfaa0"
runner.ROOT = Path("/content/hrpoly-cmp99-endpoint-reflection-chain-cold-v2")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-endpoint-reflection-chain-cold-v2-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-endpoint-reflection-chain-cold-v2-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-endpoint-reflection-chain-cold-v2-paths.txt"
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
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceNegativePhysicalDomain.lean":
        "f30658af067eeaaf942f4d143e95757680118a62f9bad76d01cb77bad7efc74c",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceNegativePhysicalDomainAudit.lean":
        "cd257952fd0e9c1d25ab09e1b619ecdf5f2db38588c16543231e57edd1dff6c4",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourcePhysicalEndpointReflection.lean":
        "3a426062c3556db30441c4e467384dd83991e9aaed8c06d0cac4428667cb7c53",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourcePhysicalEndpointReflectionAudit.lean":
        "2d0eff0e5e438f56e7e48622c4b22d9fd3afd5b2e37b9ef58aa0320728f0e749",
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
        frozenset({"YangMills.RG.cmp99SourceGeneratedFlatPhysicalPointSourceGreen_apply_eq_outerIntegrandSum"}),
    ),
    (
        "owner_character_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceOwnerCharacter"],
        None,
    ),
    (
        "owner_character_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOwnerCharacterAudit.lean"],
        frozenset({"YangMills.RG.cmp99FlatFourierMode_target_mul_source_inv_eq_ownerDifferenceCharacter"}),
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
        frozenset({"YangMills.RG.cmp99FlatFourierMode_target_mul_source_inv_eq_reversedOwnerDifferenceCharacter"}),
    ),
    (
        "negative_physical_domain_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceNegativePhysicalDomain"],
        None,
    ),
    (
        "negative_physical_domain_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceNegativePhysicalDomainAudit.lean"],
        frozenset({"YangMills.RG.cmp99SourceFlatFullPointSourceSolutionDomain_neg_physical"}),
    ),
    (
        "physical_endpoint_reflection_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullPointSourcePhysicalEndpointReflection"],
        None,
    ),
    (
        "physical_endpoint_reflection_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullPointSourcePhysicalEndpointReflectionAudit.lean"],
        frozenset({"YangMills.RG.cmp99SourceFlatFullPointSourcePhysicalFineToFineGreenIntegrand_neg_swap"}),
    ),
]


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_FOR_BOUNDED_DEBUG=1", flush=True
        )
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            from google.colab import runtime

            runtime.unassign = saved_unassign

