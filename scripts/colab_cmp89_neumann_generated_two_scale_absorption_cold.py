#!/usr/bin/env python3
"""Fresh Colab seal for generated two-scale CMP89 Neumann absorption."""

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
    "cmp89_neumann_generated_two_scale_absorption_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_GATE = {
    213: {
        "YangMills.RG.eq_zero_of_cmp89SourceNeumann_generatedTwoScale_physical_absorption",
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
runner.RUNNER_REV = "cmp89-neumann-generated-two-scale-absorption-cold-v1"
runner.SOURCE_SHA = "3213c3615d9432ee778560093303a834b0c7abe2"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-generated-two-scale-absorption-cold")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-generated-two-scale-absorption-cold-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-generated-two-scale-absorption-cold-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-generated-two-scale-absorption-cold-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannGeneratedTwoScaleAbsorption.lean":
        "3c5a98969442cc65ff1c0dab3abfccc91aff27de593f84ae5b1baff570f4f450",
    "YangMills/RG/BalabanCMP89SourceNeumannGeneratedTwoScaleAbsorptionAudit.lean":
        "1e232fc51a3bfde5cfbf6c024cdbb3e719a19bf28674aa95e5fcf817a2669f28",
}
runner.QUEUE = [
    ("generated_two_scale_absorption_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannGeneratedTwoScaleAbsorption"], None),
    ("generated_two_scale_absorption_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannGeneratedTwoScaleAbsorptionAudit.lean"], 213),
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
