#!/usr/bin/env python3
"""Fresh-checkout Colab cold seal for the directed CMP89 endpoint envelope."""

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
spec = importlib.util.spec_from_file_location("cmp89_directed_endpoint_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED = {
    201: {
        "YangMills.RG.cmp89Eq246TargetPhase_mul_finePointSourceAliasVector",
        "YangMills.RG.norm_cmp89Eq246TargetPhase_mul_finePointSourceAliasVector_signedContour",
        "YangMills.RG.norm_cmp89Eq246FinePointSourceAliasVector_signedContour",
        "YangMills.RG.norm_cmp89Eq246TargetPhase_signedContour",
        "YangMills.RG.cmp89Eq246_targetDecay_mul_sourceGrowth",
    },
    202: {
        "YangMills.RG.norm_cmp89Eq246StabilizedAliasNoncentralSourceMoment_le_of_envelope",
        "YangMills.RG.norm_cmp89Eq246StabilizedAliasFullSolutionMoment_le_of_envelope",
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
runner.RUNNER_REV = "cmp89-eq246-directed-endpoint-envelope-cold-v1"
runner.SOURCE_SHA = "06e6be132c5e7742bb60102e890814d4961b5d2a"
runner.MIN_RAM_GIB = 11.0
runner.ALLOW_GPU_RUNTIME = False
runner.ROOT = Path("/content/hrpoly-cmp89-directed-endpoint-envelope-cold-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-directed-endpoint-envelope-cold-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-directed-endpoint-envelope-cold-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-directed-endpoint-envelope-cold-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246DirectedEndpointPhase.lean":
        "f575b1601dffcea3dc97b65e0867c6a40945962d74d636ffa03e1dba81b7c983",
    "YangMills/RG/BalabanCMP89Eq246DirectedEndpointPhaseAudit.lean":
        "446cdb707c10779c92ad6bc662bc0f795b5f4c0c8bae22beb3c623cd49cac4f1",
    "YangMills/RG/BalabanCMP89Eq246SourceEnvelopeMoment.lean":
        "255e51c02c633bdf8f445ce78c81a5305217e5f27b2e0ab03db4d79ab8b62483",
    "YangMills/RG/BalabanCMP89Eq246SourceEnvelopeMomentAudit.lean":
        "6ecd46448982927f7762df6919ce02b3cc73b44b5b259484d769572f42df3278",
}
runner.QUEUE = [
    (
        "directed_endpoint_phase_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246DirectedEndpointPhase"],
        None,
    ),
    (
        "directed_endpoint_phase_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246DirectedEndpointPhaseAudit.lean"],
        201,
    ),
    (
        "source_envelope_moment_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246SourceEnvelopeMoment"],
        None,
    ),
    (
        "source_envelope_moment_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246SourceEnvelopeMomentAudit.lean"],
        202,
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
