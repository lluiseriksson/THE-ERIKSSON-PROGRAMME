#!/usr/bin/env python3
"""Fresh-checkout cold seal for the CMP89 species split and Eq. (2.48) role correction."""

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

with urllib.request.urlopen(BASE_RUNNER_URL, timeout=60) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("cmp89_eq248_source_role_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_DECLARATION_SETS = (
    {
        "YangMills.RG.cmp89SourceNeumannRegionalGaugePrecision_eq_threeSpecies",
        "YangMills.RG.cmp89SourceNeumannRegionalGaugePrecision_comp_eq_threeSpecies",
    },
    {
        "YangMills.RG.cmp89Eq248_sameScaleEndpoint_ne_fineToCoarseEndpoint_example",
    },
    {
        "YangMills.RG.cmp89Eq248PhysicalFineToCoarseGreenQprimeStar",
        "YangMills.RG.cmp89Eq248PhysicalFineToCoarseGreenQprimeStar_eq_normalized",
    },
)


def parse_axioms_exact(output: str, expected: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    without_axioms = re.findall(r"'([^']+)'doesnotdependonanyaxioms", compact)
    names = {name for name, _ in with_axioms} | set(without_axioms)
    if len(with_axioms) + len(without_axioms) != expected:
        raise RuntimeError(
            "AXIOM_BLOCK_COUNT_MISMATCH=" + repr((with_axioms, without_axioms))
        )
    if not any(len(group) == expected and names == group for group in EXPECTED_DECLARATION_SETS):
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    for name, raw_axioms in with_axioms:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)
    for name in without_axioms:
        print("AXIOM_GATE=" + name + " AXIOMS=", flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp89-eq248-source-role-cold-v1"
runner.SOURCE_SHA = "342c232fbbbb961ea8df3b8620e7681a7b557215"
runner.ROOT = Path("/content/hrpoly-cmp89-eq248-source-role-cold-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-eq248-source-role-cold-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-eq248-source-role-cold-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-eq248-source-role-cold-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannPrecisionThreeSpecies.lean":
        "cd3e03aa89809a06f1d0b9e8c233cdef564fd8a9d365f8318beff1606026a8ba",
    "YangMills/RG/BalabanCMP89NeumannPrecisionThreeSpeciesAudit.lean":
        "4404349c64655597ec26bffe759d114671fd9a0a8fdcc710682bdfa2009073e1",
    "YangMills/RG/BalabanCMP89Eq248SameScaleEndpointNoGo.lean":
        "b361186be4126adc69968ddea528840d7ad634c3e037400a7fd2fa58af39b41f",
    "YangMills/RG/BalabanCMP89Eq248SameScaleEndpointNoGoAudit.lean":
        "0da87222b54879c1a5a6df9c5190b54a17239c0cf18074972bc4b9a22d91d36f",
    "YangMills/RG/BalabanCMP89Eq248FineToCoarseGreenQprimeStar.lean":
        "aa35439a5a4a63c36777454ad7e8530636b425fa58cbd4b994621034c07fdcbf",
    "YangMills/RG/BalabanCMP89Eq248FineToCoarseGreenQprimeStarAudit.lean":
        "a051d4b9c12dd323fabfa6de7ba7c50505745d66c83cc4c49739ed68da937ceb",
}
runner.QUEUE = [
    (
        "neumann_precision_three_species_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89NeumannPrecisionThreeSpecies"],
        None,
    ),
    (
        "neumann_precision_three_species_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP89NeumannPrecisionThreeSpeciesAudit.lean"],
        2,
    ),
    (
        "eq248_same_scale_endpoint_nogo_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq248SameScaleEndpointNoGo"],
        None,
    ),
    (
        "eq248_same_scale_endpoint_nogo_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP89Eq248SameScaleEndpointNoGoAudit.lean"],
        1,
    ),
    (
        "eq248_fine_to_coarse_gqstar_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq248FineToCoarseGreenQprimeStar"],
        None,
    ),
    (
        "eq248_fine_to_coarse_gqstar_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP89Eq248FineToCoarseGreenQprimeStarAudit.lean"],
        2,
    ),
]


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print("RUNTIME_UNASSIGN_DEFERRED_FOR_DOWNLOAD=1", flush=True)
    except ImportError:
        pass
    runner_exit = runner.main()
    try:
        from google.colab import files

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    finally:
        if saved_unassign is not None:
            try:
                saved_unassign()
                print("RUNTIME_UNASSIGN_REQUESTED=1", flush=True)
            except Exception as error:
                print("RUNTIME_UNASSIGN_ERROR=" + repr(error), flush=True)
    raise SystemExit(runner_exit)
