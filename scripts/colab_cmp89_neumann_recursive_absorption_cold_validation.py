#!/usr/bin/env python3
"""Fresh Colab seal for the CMP89 Neumann recursive-absorption leaves.

The queue certifies the one-scale Poincare producer, exact parallel-defect
decomposition, quantitative recursive defect bound, and scalar kernel
absorption endpoint at one source checkpoint.  It does not provide the
source-specific recursive dictionary or attain window 15.
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
spec = importlib.util.spec_from_file_location(
    "cmp89_neumann_recursive_absorption_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_GATE = {
    121: {
        "YangMills.RG.cmp89SourceNeumann_oneScale_jointKernel",
        "YangMills.RG.exists_cmp89SourceNeumann_oneScale_poincare",
    },
    122: {
        "YangMills.RG.OrientedLatticePath.staysIn_of_physicalBondEndpointsIn",
        "YangMills.RG.cmp99SourceParallelTransportPath_staysIn_of_coarseEndpoints",
        "YangMills.RG.cmp99SourceParallelAverageDefectValue_extendZero_eq_zero",
        "YangMills.RG.covariantD0_cmp99FullSourceBlockAverage_eq_remainder_of_neumannKernel",
    },
    123: {
        "YangMills.RG.cmp99SourceCoarseTransportRemainderCochain_apply",
        "YangMills.RG.norm_restrictOneCLM_sq_le_sun",
        "YangMills.RG.restrictOne_covariantD0_cmp99FullSourceBlockAverage_eq_remainder_of_neumannKernel",
        "YangMills.RG.norm_restrictOne_cmp99SourceCoarseTransportRemainderCochain_sq_le",
    },
    124: {
        "YangMills.RG.eq_zero_of_cmp89SourceNeumannRegionalPoincare_of_derivative_sq_le",
    },
}


def parse_axioms_exact(output: str, gate: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    expected = EXPECTED_BY_GATE[gate]
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
runner.RUNNER_REV = "cmp89-neumann-recursive-absorption-cold-v1"
runner.SOURCE_SHA = "93c98c4facfa98ec772ee81b8f9498a7ada59e4c"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-recursive-absorption-cold")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-neumann-recursive-absorption-cold-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-neumann-recursive-absorption-cold-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-neumann-recursive-absorption-cold-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannOneScalePoincare.lean":
        "ddb5b7fe7f0206ce4518ae1710b5451817b8d54dc9269a2c163cd1c7022ae0a9",
    "YangMills/RG/BalabanCMP89SourceNeumannOneScalePoincareAudit.lean":
        "b6734a94fd9c11d59215f6a026da087723c70cd65b8cc5e9f7016459f77332da",
    "YangMills/RG/BalabanCMP89SourceNeumannParallelDefect.lean":
        "578edab68673d95a288a6573cb8b4384c31f096149ac86e33fb6c13c5a033815",
    "YangMills/RG/BalabanCMP89SourceNeumannParallelDefectAudit.lean":
        "12895bbf9e064c553808dc6331f52ead552b1b6ba97216317f9d7a7cc643cd43",
    "YangMills/RG/BalabanCMP89SourceNeumannRecursiveDefectBound.lean":
        "e4db267fccfd8bcfdfc451eaebb004c9589d227b495d2b8eae891b7c1e6670b7",
    "YangMills/RG/BalabanCMP89SourceNeumannRecursiveDefectBoundAudit.lean":
        "adf038d13550bc6098d27b5521960ed4cd218cd6f878d50d43561560368e778e",
    "YangMills/RG/BalabanCMP89SourceNeumannKernelAbsorption.lean":
        "b3b6500ab17d62399c20df0de91b31fdea368ef609ea8297ce1468d68a62d64d",
    "YangMills/RG/BalabanCMP89SourceNeumannKernelAbsorptionAudit.lean":
        "8b1856a6a16ef313fbdff5459fa666860074d1a1b99a82b9ae45dc2ec5d5ba51",
}
runner.QUEUE = [
    ("cmp89_neumann_one_scale_poincare_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannOneScalePoincare"], None),
    ("cmp89_neumann_one_scale_poincare_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannOneScalePoincareAudit.lean"], 121),
    ("cmp89_neumann_parallel_defect_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannParallelDefect"], None),
    ("cmp89_neumann_parallel_defect_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannParallelDefectAudit.lean"], 122),
    ("cmp89_neumann_recursive_defect_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannRecursiveDefectBound"], None),
    ("cmp89_neumann_recursive_defect_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannRecursiveDefectBoundAudit.lean"], 123),
    ("cmp89_neumann_kernel_absorption_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannKernelAbsorption"], None),
    ("cmp89_neumann_kernel_absorption_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannKernelAbsorptionAudit.lean"], 124),
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
