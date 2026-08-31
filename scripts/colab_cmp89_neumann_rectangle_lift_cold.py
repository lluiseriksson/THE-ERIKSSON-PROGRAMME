#!/usr/bin/env python3
"""Fresh Colab seal for the exact CMP89 complete-block rectangle lift."""

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
    "cmp89_neumann_rectangle_lift_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_DECLARATIONS = {
    "YangMills.RG.cmp89SourceNeumannScaleRectangleSide",
    "YangMills.RG.cmp89SourceNeumannScaleRectangleSidePow",
    "YangMills.RG.cmp99LiftActiveRegion_cmp89Rectangle_eq",
    "YangMills.RG.cmp99IteratedLiftActiveRegion_cmp89Rectangle_eq",
    "YangMills.RG.cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv",
    "YangMills.RG.cmp89SourceNeumannLiftedRectangleSiteEquiv",
}


def parse_axioms_exact(output: str, expected: int) -> None:
    if expected != len(EXPECTED_DECLARATIONS):
        raise RuntimeError("UNEXPECTED_AXIOM_GATE=" + str(expected))
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(
        r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact
    )
    without_axioms = re.findall(
        r"'([^']+)'doesnotdependonanyaxioms", compact
    )
    names = {name for name, _ in with_axioms} | set(without_axioms)
    if len(with_axioms) + len(without_axioms) != expected:
        raise RuntimeError(
            "AXIOM_BLOCK_COUNT_MISMATCH="
            + repr((with_axioms, without_axioms))
        )
    if names != EXPECTED_DECLARATIONS:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    for name, raw_axioms in with_axioms:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print(
            "AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)),
            flush=True,
        )
    for name in without_axioms:
        print("AXIOM_GATE=" + name + " AXIOMS=", flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp89-neumann-rectangle-lift-cold-v1"
runner.SOURCE_SHA = "66ac2a94835de099070055d9e0bc18ab40fcab6f"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-rectangle-lift-cold")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-rectangle-lift-cold-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-rectangle-lift-cold-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-rectangle-lift-cold-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannRectangleLift.lean":
        "15f26773e493b7aba3555f5d1f741f6af59c781fcf3cf8beb863b4949244717f",
    "YangMills/RG/BalabanCMP89NeumannRectangleLiftAudit.lean":
        "9138470d451f501eec84122b9fca3fdfe04cf488a60d797c1441c5c3d1ad62a6",
}
runner.QUEUE = [
    (
        "neumann_rectangle_lift_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89NeumannRectangleLift"],
        None,
    ),
    (
        "neumann_rectangle_lift_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP89NeumannRectangleLiftAudit.lean",
        ],
        6,
    ),
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
