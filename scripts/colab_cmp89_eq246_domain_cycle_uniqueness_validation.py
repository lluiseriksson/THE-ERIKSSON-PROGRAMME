#!/usr/bin/env python3
"""Fresh-checkout cold queue for three independent CMP89 (2.46) leaves."""

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
spec = importlib.util.spec_from_file_location("cmp89_domain_cycle_uniqueness_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED = {
    309: {
        "YangMills.RG.CMP89Eq246FullSolutionDomain",
        "YangMills.RG.cmp89Eq246FullSolutionDomain_of_commonRadius",
    },
    310: {
        "YangMills.RG.cmp89Eq246EntireAliasFineSymbol_physicalShift_eq_cycle",
        "YangMills.RG.cmp89Eq246EntireAliasAverageColumn_physicalShift_eq_cycle",
        "YangMills.RG.cmp89Eq246EntireAliasAverageRow_physicalShift_eq_cycle",
        "YangMills.RG.cmp89Eq246FinePointSourceAliasVector_physicalShift_eq_cycle",
        "YangMills.RG.exp_I_cmp89Eq246TargetPhase_physicalShift_eq_cycle",
    },
    311: {
        "YangMills.RG.cmp89Eq246EntireAliasPrecisionMatrix_mulVec_injective",
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
runner.RUNNER_REV = "cmp89-eq246-domain-cycle-uniqueness-cold-v2"
runner.SOURCE_SHA = "df364a3c629004ff7ca1062247cfe488b0579f2e"
runner.MIN_RAM_GIB = 11.0
runner.ALLOW_GPU_RUNTIME = False
runner.ROOT = Path("/content/hrpoly-cmp89-eq246-domain-cycle-uniqueness-cold-v2")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-eq246-domain-cycle-uniqueness-cold-v2-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-eq246-domain-cycle-uniqueness-cold-v2-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-eq246-domain-cycle-uniqueness-cold-v2-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246FullSolutionDomain.lean":
        "daf253d68199083ed3a71e2890db08b94d782222c9dfd69b28ff004c62bd60e2",
    "YangMills/RG/BalabanCMP89Eq246FullSolutionDomainAudit.lean":
        "12d9c9525e0b2fbff6454a85288e8b025b2346319ca6c988f017f9e028181738",
    "YangMills/RG/BalabanCMP89Eq246AliasCycleTransport.lean":
        "8f6ffae2b417589d4c61aa00320666bd72fd1be0b4756580afb8508304ce13f7",
    "YangMills/RG/BalabanCMP89Eq246AliasCycleTransportAudit.lean":
        "69f73e6d66806fea6aa538a3d2cb4d26ce9158a2c7b162a0ff5ae0eb3fe4cb88",
    "YangMills/RG/BalabanCMP89Eq246AliasPrecisionUniqueness.lean":
        "2f3c56ca5fc423d2ffb0d1d42f6e5f67b9a6fb220da4422fe706381771127411",
    "YangMills/RG/BalabanCMP89Eq246AliasPrecisionUniquenessAudit.lean":
        "34f662592715346047d55a979e77ccf8d9dab5fe94078ee546b3be7625793bf9",
}
runner.QUEUE = [
    (
        "full_solution_domain_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246FullSolutionDomain"],
        None,
    ),
    (
        "full_solution_domain_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246FullSolutionDomainAudit.lean"],
        309,
    ),
    (
        "alias_cycle_transport_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246AliasCycleTransport"],
        None,
    ),
    (
        "alias_cycle_transport_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246AliasCycleTransportAudit.lean"],
        310,
    ),
    (
        "alias_precision_uniqueness_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246AliasPrecisionUniqueness"],
        None,
    ),
    (
        "alias_precision_uniqueness_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246AliasPrecisionUniquenessAudit.lean"],
        311,
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
