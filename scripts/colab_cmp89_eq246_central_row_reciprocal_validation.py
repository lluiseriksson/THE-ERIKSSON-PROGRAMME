#!/usr/bin/env python3
"""Cold Colab gate for the CMP89 Eq. (2.46) central-row reciprocal bound."""

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
spec = importlib.util.spec_from_file_location("cmp89_eq246_row_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED = {
    71: {
        "YangMills.RG.cmp89Eq246CentralAverageRowReciprocalBound",
        "YangMills.RG.norm_inv_cmp89Eq246CentralAverageRow_le",
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
runner.RUNNER_REV = "cmp89-eq246-central-row-reciprocal-cold-v1"
runner.SOURCE_SHA = "4584f4c9d2cebe4f61a1ec48681256260deb7090"
runner.MIN_RAM_GIB = 11.0
runner.ALLOW_GPU_RUNTIME = False
runner.ROOT = Path("/content/hrpoly-cmp89-eq246-central-row-reciprocal-cold-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-eq246-central-row-reciprocal-cold-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-eq246-central-row-reciprocal-cold-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-eq246-central-row-reciprocal-cold-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246CentralAverageRowReciprocalBound.lean":
        "7b2fd3fa817da416cd7507459997d3aa3d95afc3b62b8632f8211e06a6286f3d",
    "YangMills/RG/BalabanCMP89Eq246CentralAverageRowReciprocalBoundAudit.lean":
        "cf431cf3f192f6cc24155e88a4893cef558bca4bfa552df2b81da612068e380e",
}
runner.QUEUE = [
    (
        "central_row_reciprocal_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq246CentralAverageRowReciprocalBound"],
        None,
    ),
    (
        "central_row_reciprocal_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP89Eq246CentralAverageRowReciprocalBoundAudit.lean"],
        71,
    ),
]


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print("RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True)
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            from google.colab import runtime

            runtime.unassign = saved_unassign
