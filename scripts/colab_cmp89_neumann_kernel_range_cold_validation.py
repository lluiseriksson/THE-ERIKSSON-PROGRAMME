#!/usr/bin/env python3
"""Fresh Colab seal for the exact CMP89 Neumann kernel/range leaves.

The cold queue seals internal-bond transport, path transport and the literal
one-scale ``Qdagger Q`` range identity at one source checkpoint.  It does not
prove recursive tower transport, the terminal joint-kernel theorem, a
uniform Poincare constant, window 15, or any terminal ``TermSource`` field.
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
spec = importlib.util.spec_from_file_location("cmp89_neumann_kernel_range_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_GATE = {
    111: {
        "YangMills.RG.cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_internalBond",
    },
    112: {
        "YangMills.RG.cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_pathTransport",
    },
    113: {
        "YangMills.RG.cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_blockAverage",
        "YangMills.RG.cmp89SourceNeumannRegionalCovariantD0CLM_eq_zero_weightedAdjoint_average",
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
runner.RUNNER_REV = "cmp89-neumann-kernel-range-cold-v1"
runner.SOURCE_SHA = "fd4ca187d4e943c446177ec26d920f6740a87dab"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-kernel-range-cold")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-neumann-kernel-range-cold-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-neumann-kernel-range-cold-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-neumann-kernel-range-cold-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannInternalBondTransport.lean":
        "3ca601ce233d3c5da92572058677b71a3a4e5d97ce92c50fe3999f1715270913",
    "YangMills/RG/BalabanCMP89SourceNeumannInternalBondTransportAudit.lean":
        "7b339d2fd3aeb5f965fc5985ed01b504d6a1684e0cb246897d164427e11c5320",
    "YangMills/RG/BalabanCMP89SourceNeumannPathTransport.lean":
        "9147a2ecd753cf68bde1707fd90e15610b04309f71985bf89481efdc36b14e8d",
    "YangMills/RG/BalabanCMP89SourceNeumannPathTransportAudit.lean":
        "342404b048690f783be814ee49d823236938d41b6a3f875687c1d70767444670",
    "YangMills/RG/BalabanCMP89SourceNeumannOneScaleRange.lean":
        "55fe6ac6df9f07156ba87fadc980193298732426cb4c39f33d2e37fba88a14be",
    "YangMills/RG/BalabanCMP89SourceNeumannOneScaleRangeAudit.lean":
        "5672fb425b1693f45d93c303fad125cfbf491e8d788a0999e5e44af9661bee94",
}
runner.QUEUE = [
    ("cmp89_neumann_internal_bond_transport_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannInternalBondTransport"], None),
    ("cmp89_neumann_internal_bond_transport_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannInternalBondTransportAudit.lean"], 111),
    ("cmp89_neumann_path_transport_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannPathTransport"], None),
    ("cmp89_neumann_path_transport_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannPathTransportAudit.lean"], 112),
    ("cmp89_neumann_one_scale_range_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP89SourceNeumannOneScaleRange"], None),
    ("cmp89_neumann_one_scale_range_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceNeumannOneScaleRangeAudit.lean"], 113),
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
