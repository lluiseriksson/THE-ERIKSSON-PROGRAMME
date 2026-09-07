#!/usr/bin/env python3
"""Fresh Colab seal for the CMP89 Neumann/Dirichlet boundary no-go.

This gate validates the source-faithful internal-bond Neumann precision and
the exact boundary-crossing obstruction to identifying it with the existing
zero-extension Dirichlet derivative.  It does not compare Green norms,
construct CMP89 (2.42), attain window 15, move ``20/41`` or instantiate a
``TermSource``.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
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
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("cmp89_neumann_nogo_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_COUNT = {
    2: {
        "YangMills.RG.inner_cmp89SourceNeumannRegionalLaplacian",
        "YangMills.RG.cmp89SourceNeumannRegionalLaplacian_isSymmetric",
    },
    3: {
        "YangMills.RG."
        "cmp89SourceNeumannRegionalCovariantD0CLM_boundary_eq_zero",
        "YangMills.RG.cmp99ActiveRegionSourceCovariantD0CLM_boundary_eq",
        "YangMills.RG."
        "cmp89SourceNeumannRegionalCovariantD0CLM_ne_dirichlet_of_boundary",
    },
}


def parse_axioms_exact(output: str, expected_count: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    expected = EXPECTED_BY_COUNT[expected_count]
    if set(found) != expected:
        raise RuntimeError(
            "AXIOM_DECLARATIONS_MISMATCH="
            + repr({"found": sorted(found), "expected": sorted(expected)})
        )
    for name in sorted(expected):
        axioms = {item for item in found[name].split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp89-neumann-dirichlet-boundary-nogo-v1"
runner.SOURCE_SHA = "1721fb8b8655e4e6f9bb15fc0e0440750ff013d9"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-dirichlet-boundary-nogo")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-dirichlet-boundary-nogo-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-dirichlet-boundary-nogo-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-dirichlet-boundary-nogo-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalPrecision.lean":
        "6b7bd0dca8e66012fd29f88ee127ba03d79872b539abcb202ebb38332cb15e68",
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalPrecisionAudit.lean":
        "eb8cb9d56a7f1dd3bdff5b423a5deb8effa4bb98b524963e8dcf9e3d80cd9838",
    "YangMills/RG/BalabanCMP89NeumannDirichletBoundaryNoGo.lean":
        "b499f7aba1d39a66ca95efb78cb6277702aff4b72e435e58c9e20d761449b6f1",
    "YangMills/RG/BalabanCMP89NeumannDirichletBoundaryNoGoAudit.lean":
        "d3465d86f9eea7c76655df7575e5daecb2633b3e877d1e9851dcb7bd2b14ca8b",
    "YangMillsCore.lean":
        "9a9b20f2ed0100ca668bfb1534fa22c00aef03dfdc8958e497667526b8bbc8ea",
}
runner.QUEUE = [
    (
        "cmp89_source_neumann_precision_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP89SourceNeumannRegionalPrecision",
        ],
        None,
    ),
    (
        "cmp89_source_neumann_precision_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP89SourceNeumannRegionalPrecisionAudit.lean",
        ],
        2,
    ),
    (
        "cmp89_neumann_dirichlet_boundary_nogo_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP89NeumannDirichletBoundaryNoGo",
        ],
        None,
    ),
    (
        "cmp89_neumann_dirichlet_boundary_nogo_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP89NeumannDirichletBoundaryNoGoAudit.lean",
        ],
        3,
    ),
    (
        "cmp89_neumann_dirichlet_boundary_nogo_root",
        ["lake", "build", "YangMillsCore"],
        None,
    ),
]


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    runner_exit = runner.main()
    try:
        from google.colab import files

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(runner_exit)
