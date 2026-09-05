#!/usr/bin/env python3
"""Fresh Colab seal for the exact regional Neumann derivative split."""

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
spec = importlib.util.spec_from_file_location(
    "cmp89_neumann_coarse_derivative_decomposition_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_DECLARATIONS = {
    "YangMills.RG.cmp99SourceParallelAverageDefectCochain",
    "YangMills.RG.cmp99SourceParallelAverageDefectCochain_apply",
    "YangMills.RG.restrictOne_covariantD0_cmp99FullSourceBlockAverage_eq_defect_add_remainder",
    "YangMills.RG.cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_eq_twoSpecies",
}


def parse_axioms_exact(output: str, expected: int) -> None:
    if expected != len(EXPECTED_DECLARATIONS):
        raise RuntimeError("UNEXPECTED_AXIOM_GATE=" + str(expected))
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    names = {name for name, _ in blocks}
    if len(blocks) != expected or names != EXPECTED_DECLARATIONS:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(blocks))
    for name, raw_axioms in blocks:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print(
            "AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)),
            flush=True,
        )


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp89-neumann-coarse-derivative-decomposition-cold-v1"
runner.SOURCE_SHA = "138b265386fcdc2216746737ef4dee5f4da87f27"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-coarse-derivative-decomposition-cold")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-coarse-derivative-decomposition-cold-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-coarse-derivative-decomposition-cold-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-coarse-derivative-decomposition-cold-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannCoarseDerivativeDecomposition.lean":
        "e476ef288a9b517cdb2756a22e6733f438b497818c1b883f4df44bfccf02022d",
    "YangMills/RG/BalabanCMP89SourceNeumannCoarseDerivativeDecompositionAudit.lean":
        "a929bdfeadfec0803e2c93ef489827bba0e3c0e99a75bcda222f1a865ed3801f",
}
runner.QUEUE = [
    ("coarse_derivative_decomposition_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannCoarseDerivativeDecomposition"], None),
    ("coarse_derivative_decomposition_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannCoarseDerivativeDecompositionAudit.lean"], 4),
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
