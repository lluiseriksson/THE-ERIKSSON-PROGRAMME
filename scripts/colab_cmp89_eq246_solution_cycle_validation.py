#!/usr/bin/env python3
"""Fresh-checkout cold queue for CMP89 (2.46) precision and solution cycling."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
import urllib.request


BASE_RUNNER = Path("/content/colab_qprime_row_validation.py")
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "2dfaa8634203470608cc341d36e5d1fab4a546c4/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = "2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e"

with urllib.request.urlopen(BASE_RUNNER_URL, timeout=60) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("cmp89_solution_cycle_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED = {
    312: {
        "YangMills.RG.cmp89Eq246EntireAliasPrecisionMatrix_physicalShift_eq_cycle",
        "YangMills.RG.cmp89Eq246EntireAliasPrecisionMatrix_mulVec_physicalShift_eq_cycle",
    },
    313: {
        "YangMills.RG.cmp89Eq246StabilizedFinePointSourceSolution_physicalShift_eq_cycle",
    },
}


def parse_axioms_exact(output: str, expected_key: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    without_axioms = re.findall(r"'([^']+)'doesnotdependonanyaxioms", compact)
    names = {name for name, _ in with_axioms} | set(without_axioms)
    expected_names = EXPECTED.get(expected_key)
    if expected_names is None:
        raise RuntimeError("UNEXPECTED_AXIOM_GATE_KEY=" + str(expected_key))
    if len(with_axioms) + len(without_axioms) != len(expected_names):
        raise RuntimeError("AXIOM_BLOCK_COUNT_MISMATCH=" + repr((with_axioms, without_axioms)))
    if names != expected_names:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    for name, raw_axioms in with_axioms:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)
    for name in without_axioms:
        print("AXIOM_GATE=" + name + " AXIOMS=", flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp89-eq246-solution-cycle-cold-v1"
runner.SOURCE_SHA = "e9f8f326262588c2c12ee98daa8e276cb0b63001"
runner.MIN_RAM_GIB = 11.0
runner.ALLOW_GPU_RUNTIME = False
runner.ROOT = Path("/content/hrpoly-cmp89-eq246-solution-cycle-cold-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-eq246-solution-cycle-cold-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-eq246-solution-cycle-cold-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-eq246-solution-cycle-cold-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246AliasPrecisionCycle.lean":
        "7f921295a0130adae8ae099b256ce251b3340bfd75cf5de755e07b9cafa98f48",
    "YangMills/RG/BalabanCMP89Eq246AliasPrecisionCycleAudit.lean":
        "22d58cb00ecf947e7c90e7e172300fcd43bd3c90e605b2b400255ea60b52050f",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceSolutionCycle.lean":
        "b8101d95a2bd66657ab58974ccf0eb2b22b685de219bfbd516bf973cc7e1130c",
    "YangMills/RG/BalabanCMP89Eq246FinePointSourceSolutionCycleAudit.lean":
        "85f20825891ebd6da1bc3603d26c9c026898b3ac3e565a64a4020dfc38472ebc",
}
runner.QUEUE = [
    (
        "alias_precision_cycle_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246AliasPrecisionCycle"],
        None,
    ),
    (
        "alias_precision_cycle_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246AliasPrecisionCycleAudit.lean"],
        312,
    ),
    (
        "fine_point_source_solution_cycle_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246FinePointSourceSolutionCycle"],
        None,
    ),
    (
        "fine_point_source_solution_cycle_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246FinePointSourceSolutionCycleAudit.lean"],
        313,
    ),
]


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print("RUNTIME_RETAINED_FOR_EVIDENCE_DOWNLOAD=1", flush=True)
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            from google.colab import runtime

            runtime.unassign = saved_unassign
