#!/usr/bin/env python3
"""Fresh-checkout cold gate for the generated physical residue-class composition.

The runner is pinned to one immutable PRE-VALIDATION source checkpoint and
reuses only the already sealed fail-closed runner implementation.  It restores
no project ``.lake/build`` graph and stops on the first focal or axiom error.
Passing this gate does not move ``20/41``, attain window 15 or instantiate a
``TermSource``.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


HERE = Path("/content")
BASE_RUNNER = HERE / "colab_cmp99_endpoint_reflection_chain_cold_v2.py"
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "882d0cd70c79390a4ae4a2318ea91958dd9e9731/"
    "scripts/colab_cmp99_endpoint_reflection_chain_cold.py"
)
BASE_RUNNER_SHA256 = (
    "c8afd717397ce8b60e20ac91eb031e60992c705dc17c059e988a5ffc80616384"
)

with urllib.request.urlopen(BASE_RUNNER_URL, timeout=60) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)

spec = importlib.util.spec_from_file_location(
    "cmp99_endpoint_reflection_chain_cold_v2", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
runner = base.runner

runner.RUNNER_REV = "cmp99-generated-residue-class-cold-v3"
runner.SOURCE_SHA = "440afa7b0883cc77a30f2457c879b025dcde32f1"
runner.ROOT = Path("/content/hrpoly-cmp99-generated-residue-class-cold-v3")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-generated-residue-class-cold-v3-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-generated-residue-class-cold-v3-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-generated-residue-class-cold-v3-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceResidueClass.lean":
        "90a7f6c6b29f0dd9c2c260d199c62e03f62f000bef2f9b8b82dce1d35814da1a",
    "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceResidueClassAudit.lean":
        "b9f6fcee2fc3760ab7893f0836c8e566cdd4f0847b7fb6a2a2f5356e50f66732",
}

runner.QUEUE = [
    (
        "generated_residue_class_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPointSourceResidueClass",
        ],
        None,
    ),
    (
        "generated_residue_class_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalPointSourceResidueClassAudit.lean",
        ],
        frozenset({
            "YangMills.RG.cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum",
            "YangMills.RG.cmp99SourceGeneratedFlatPhysicalPointSourceGreenValue",
            "YangMills.RG.CMP99SourceGeneratedFlatPhysicalPointSourceResidueClassCertificate.eq_scaledResidueClass",
            "YangMills.RG.cmp99SourceGeneratedFlatPhysicalPointSourceGreen_apply_eq_scaledResidueClass",
        }),
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
