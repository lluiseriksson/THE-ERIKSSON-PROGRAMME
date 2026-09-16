"""Fresh Colab seal for the repaired final full-G aliasing pair.

The preceding cold gate validated the first five focal/audit pairs and stopped
at this final focal.  This runner uses a new checkout and build graph, verifies
the repaired source bytes, and runs only the changed focal plus its unchanged
exact audit.  It retains the runtime so the evidence can be downloaded before
disconnecting.
"""

from pathlib import Path
import hashlib
import importlib.util
import urllib.request


PARENT_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "d5946c390cd39df9c9a74ccca6fdaa6fd553e988/"
    "scripts/colab_cmp89_mass_uniform_cold_validation.py"
)
PARENT_SHA256 = "baec81104da84649159e30298ad7b547096e00bff362776e347386657014158a"
PARENT = Path("/content/colab_cmp89_mass_uniform_cold_validation.py")

with urllib.request.urlopen(PARENT_URL, timeout=60) as response:
    parent_source = response.read()
parent_hash = hashlib.sha256(parent_source).hexdigest()
print("PARENT_RUNNER_TRANSPORT_SHA256=" + parent_hash, flush=True)
if parent_hash != PARENT_SHA256:
    raise RuntimeError("PARENT_RUNNER_TRANSPORT_HASH_MISMATCH")
PARENT.write_bytes(parent_source)
spec = importlib.util.spec_from_file_location("cmp89_mass_uniform_parent", PARENT)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load parent runner: {PARENT}")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "cmp89-mass-uniform-final-aliasing-cold-v1"
runner.SOURCE_SHA = "286719b94b6cfcf9b2ea45a02951277149f2f065"
runner.MIN_RAM_GIB = 11.0
runner.ALLOW_GPU_RUNTIME = False
runner.ROOT = Path("/content/hrpoly-cmp89-mass-uniform-final-aliasing-cold-v1")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-mass-uniform-final-aliasing-cold-v1-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-mass-uniform-final-aliasing-cold-v1-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-mass-uniform-final-aliasing-cold-v1-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99FullGreenFiniteGridAliasing.lean":
        "6b2f66f90a14a324d47b23f952d409a3154a16240317ddc1d673ac67900a0694",
    "YangMills/RG/BalabanCMP99FullGreenFiniteGridAliasingAudit.lean":
        "978468765b91ec8c59c59d10c9680c1b181571e1ce8c58cc3dbdbe06f9467756",
}
runner.QUEUE = [
    (
        "full_green_finite_grid_aliasing_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99FullGreenFiniteGridAliasing"],
        None,
    ),
    (
        "full_green_finite_grid_aliasing_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99FullGreenFiniteGridAliasingAudit.lean",
        ],
        406,
    ),
]


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print(
            "RUNTIME_RETAINED_FOR_DEBUG_OR_EVIDENCE=1", flush=True
        )
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            from google.colab import runtime

            runtime.unassign = saved_unassign
