#!/usr/bin/env python3
"""Fresh Colab seal for two-scale physical CMP89 Neumann absorption."""

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
    "cmp89_neumann_two_scale_physical_absorption_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_GATE = {
    211: {
        "YangMills.RG.eq_zero_of_cmp89SourceNeumann_twoScale_physical_absorption",
    },
    212: {
        "YangMills.RG.cmp89SourceNeumannPhysicalOneStepGate_d4_M4_q8_eq",
        "YangMills.RG.cmp89SourceNeumannPhysicalOneStepGate_d4_M4_q8_lt_one",
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
runner.RUNNER_REV = "cmp89-neumann-two-scale-physical-absorption-cold-v1"
runner.SOURCE_SHA = "8c03a9e58f3195b54176f483aee2543343c0e88f"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-two-scale-physical-absorption-cold")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-two-scale-physical-absorption-cold-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-two-scale-physical-absorption-cold-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-two-scale-physical-absorption-cold-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannTwoScalePhysicalAbsorption.lean":
        "ccbcdc5b50ce8b1d80e7d4c79fa4686aab0a16eb113911e60c16821c25841ebb",
    "YangMills/RG/BalabanCMP89SourceNeumannTwoScalePhysicalAbsorptionAudit.lean":
        "530395fbfa1f3d79260c487585adf16fb754c5bed1ccf164b11327c12b858fd3",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateWitness.lean":
        "9bcc6d7cef4ab730d53ed2d97783521d348881828a1609c0d8887567b30650e8",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateWitnessAudit.lean":
        "8026566164e40f2dd797bb6031f2c6b97a367a27c3d340d96315809e93dea901",
}
runner.QUEUE = [
    ("two_scale_physical_absorption_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannTwoScalePhysicalAbsorption"], None),
    ("two_scale_physical_absorption_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannTwoScalePhysicalAbsorptionAudit.lean"], 211),
    ("physical_gate_witness_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannPhysicalGateWitness"], None),
    ("physical_gate_witness_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannPhysicalGateWitnessAudit.lean"], 212),
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
