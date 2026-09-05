#!/usr/bin/env python3
"""Fresh Colab seal for the restricted Neumann straight-path energy bound."""

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
    "cmp89_neumann_restricted_straight_path_energy_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_DECLARATIONS = {
    "YangMills.RG.cmp89SourceNeumannParallelFineBondAt_injective",
    "YangMills.RG.cmp89SourceNeumannParallelFineBondAt_mem_bonds",
    "YangMills.RG.sum_covariantPathEnergy_cmp99StraightPositivePath_le_neumannRaw",
    "YangMills.RG.sum_cmp89SourceNeumannParallelPathEnergy_le_raw",
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
runner.RUNNER_REV = "cmp89-neumann-restricted-straight-path-energy-cold-v1"
runner.SOURCE_SHA = "928d3b8f8c62df8590687a3ee9edc58459386ad6"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-restricted-straight-path-energy-cold")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-restricted-straight-path-energy-cold-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-restricted-straight-path-energy-cold-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-restricted-straight-path-energy-cold-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannRestrictedStraightPathEnergy.lean":
        "2b57757e353555d945fbdf51d5b72c126918fba048f61f7bfb6d2872804186f8",
    "YangMills/RG/BalabanCMP89SourceNeumannRestrictedStraightPathEnergyAudit.lean":
        "321654a1277031d2165580ba7be29e0e6dd7c543982ae733f03f642caf0d5964",
}
runner.QUEUE = [
    ("restricted_straight_path_energy_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannRestrictedStraightPathEnergy"], None),
    ("restricted_straight_path_energy_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannRestrictedStraightPathEnergyAudit.lean"], 4),
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
