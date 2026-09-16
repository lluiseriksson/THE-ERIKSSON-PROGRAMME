#!/usr/bin/env python3
"""Fresh Colab seal for the reached generated two-scale Neumann gate."""

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
    "cmp89_neumann_generated_two_scale_gate_reachability_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_DECLARATION = (
    "YangMills.RG."
    "exists_pos_cmp89SourceNeumann_generatedTwoScale_physical_absorption_radius"
)


def parse_axioms_exact(output: str, expected: int) -> None:
    if expected != 216:
        raise RuntimeError("UNEXPECTED_AXIOM_GATE=" + str(expected))
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    if len(blocks) != 1 or blocks[0][0] != EXPECTED_DECLARATION:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(blocks))
    axioms = {item for item in blocks[0][1].split(",") if item}
    if not axioms.issubset(runner.ALLOWED_AXIOMS):
        raise RuntimeError("AXIOM_SET=" + repr(sorted(axioms)))
    print(
        "AXIOM_GATE=" + EXPECTED_DECLARATION
        + " AXIOMS=" + ",".join(sorted(axioms)),
        flush=True,
    )


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp89-neumann-generated-two-scale-gate-reachability-cold-v1"
runner.SOURCE_SHA = "8f03fc36022487e7fff32a2989055ad36b628de2"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-generated-two-scale-gate-cold")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-generated-two-scale-gate-cold-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-generated-two-scale-gate-cold-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-generated-two-scale-gate-cold-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannGeneratedTwoScaleGateReachability.lean":
        "de78a88541358ee9b670bf78046af3cbda7764e2e6edaa48ef21a6bfe3fb5217",
    "YangMills/RG/BalabanCMP89SourceNeumannGeneratedTwoScaleGateReachabilityAudit.lean":
        "0aa92987547320ac94f94fd1afeaee5f528a1ce4027a0af446ec4b51698995a6",
}
runner.QUEUE = [
    ("generated_two_scale_gate_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannGeneratedTwoScaleGateReachability"], None),
    ("generated_two_scale_gate_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannGeneratedTwoScaleGateReachabilityAudit.lean"], 216),
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
