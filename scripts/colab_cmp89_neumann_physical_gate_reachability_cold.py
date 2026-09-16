#!/usr/bin/env python3
"""Fresh Colab seal for physical Neumann gate reachability."""

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
    "cmp89_neumann_physical_gate_reachability_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_GATE = {
    214: {
        "YangMills.RG.cmp89SourceNeumannPhysicalOneStepDefectCoefficient_mono",
        "YangMills.RG.cmp89SourceNeumannPhysicalOneStepGate_lt_one_of_le_d4_M4_q8",
        "YangMills.RG.cmp89SourceNeumannPhysicalOneStepGate_lt_one_of_radius_bounds_d4_M4",
    },
    215: {
        "YangMills.RG.exists_pos_cmp89SourceNeumann_twoScale_physical_gate_radius",
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
runner.RUNNER_REV = "cmp89-neumann-physical-gate-reachability-cold-v1"
runner.SOURCE_SHA = "b85e7f8a401e82971889eebe50b5a10875c2046b"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-physical-gate-reachability-cold")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-physical-gate-reachability-cold-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-physical-gate-reachability-cold-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-physical-gate-reachability-cold-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateMonotonicity.lean":
        "ebf14e1b4ff9d0eca2dc4d38d25144d3fa3523c5c938ccef681d33f7fb772c13",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateMonotonicityAudit.lean":
        "15b27529a20769cd9b10f3170b462d71232fe025838970e1dbd357ceae13fe55",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateReachability.lean":
        "8ef619caf22b54d6893dc2ee2b869e1b67305816cbc0dbcaf48e1ffbd0d8ef82",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateReachabilityAudit.lean":
        "c122ee5f3dead42e76ef8dafcf17d87db3eb3a267aa19130cc97ac7dd6f437f4",
}
runner.QUEUE = [
    ("physical_gate_monotonicity_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannPhysicalGateMonotonicity"], None),
    ("physical_gate_monotonicity_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateMonotonicityAudit.lean"], 214),
    ("physical_gate_reachability_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannPhysicalGateReachability"], None),
    ("physical_gate_reachability_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateReachabilityAudit.lean"], 215),
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
