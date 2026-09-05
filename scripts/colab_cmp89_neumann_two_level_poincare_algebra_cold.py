#!/usr/bin/env python3
"""Fresh Colab seal for two-level Poincare feedback algebra."""

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
    "cmp89_neumann_two_level_poincare_algebra_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_DECLARATIONS = {
    "YangMills.RG.le_twoLevelPoincare_of_feedback_lt_one",
    "YangMills.RG.norm_sq_le_twoLevelPoincare_of_derivative_feedback",
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
runner.RUNNER_REV = "cmp89-neumann-two-level-poincare-algebra-cold-v1"
runner.SOURCE_SHA = "3d23e4036b9260b24b7e7a5106c8dad9b2e94b28"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-two-level-poincare-algebra-cold")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-two-level-poincare-algebra-cold-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-two-level-poincare-algebra-cold-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-two-level-poincare-algebra-cold-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannTwoLevelPoincareAlgebra.lean":
        "ec50cd8f9d4884272d9634ae502dd89ef650eecd1b149c5bbab5c1fbbd2bcd7a",
    "YangMills/RG/BalabanCMP89SourceNeumannTwoLevelPoincareAlgebraAudit.lean":
        "8fc54d2cfff769d7e2483fdf93210d36de166b57ba2205f44f6c535f4cf5866a",
}
runner.QUEUE = [
    ("two_level_poincare_algebra_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannTwoLevelPoincareAlgebra"], None),
    ("two_level_poincare_algebra_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannTwoLevelPoincareAlgebraAudit.lean"], 2),
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
