#!/usr/bin/env python3
"""Hash-gated Colab validation for the generated/full-complex mass dictionary.

This instrumentation-only wrapper specializes the generic fresh-clone runner
to one immutable PRE-VALIDATION source checkpoint and its two exact Git blobs.
It does not alter the mathematical source under validation.
"""

from __future__ import annotations

import hashlib
import urllib.request
from pathlib import Path


BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/1e7621516004e62634091a45511212f1db4bc484/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)

REPRO_PATH = Path("/content/generated-qprime-complex-coordinate-smul-repro.lean")
REPRO_SOURCE = """import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.RCLike.Basic

example {n : ℕ} (r : ℝ) (v : EuclideanSpace ℂ (Fin n)) (a : Fin n) :
    (r • v).ofLp a = (r : ℂ) * v.ofLp a := by
  simp only [WithLp.ofLp_smul, Pi.smul_apply]
  rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
"""


def main() -> int:
    with urllib.request.urlopen(BASE_RUNNER_URL) as response:
        base_source = response.read()
    actual = hashlib.sha256(base_source).hexdigest()
    print("BASE_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
    if actual != BASE_RUNNER_SHA256:
        raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")

    namespace: dict[str, object] = {"__name__": "colab_validation_base"}
    exec(compile(base_source, BASE_RUNNER_URL, "exec"), namespace)
    namespace.update(
        {
            "RUNNER_REV": "generated-qprime-mass-complex-coordinate-dictionary-v8",
            "SOURCE_SHA": "4f72af55fdcb3755d4cb90b0dbc34189ac2a7af0",
            "ROOT": Path("/content/hrpoly-generated-qprime-mass-complex-dictionary"),
            "EVIDENCE": Path(
                "/content/hrpoly-generated-qprime-mass-complex-dictionary-evidence"
            ),
            "ARCHIVE": Path(
                "/content/hrpoly-generated-qprime-mass-complex-dictionary-evidence.tar.gz"
            ),
            "PATH_MANIFEST": Path(
                "/content/hrpoly-generated-qprime-mass-complex-dictionary-paths.txt"
            ),
            "SOURCE_BLOBS": {
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeMassComplexCoordinateDictionary.lean":
                    "d53117dfdf5edfe1c70fbc2efe0765852301b574c11b004b0d734700048e1a15",
                "YangMills/RG/BalabanCMP99SourceFlatGeneratedQprimeMassComplexCoordinateDictionaryAudit.lean":
                    "8e408cbea90867f2b1a8d1572ae61767e7cbcf72c720cfdffec0a8fc3934edef",
            },
            "QUEUE": [
                (
                    "generated_qprime_complex_coordinate_smul_repro",
                    ["lake", "env", "lean", str(REPRO_PATH)],
                    None,
                ),
                (
                    "generated_qprime_mass_complex_coordinate_dictionary_focal",
                    [
                        "lake",
                        "build",
                        "YangMills.RG."
                        "BalabanCMP99SourceFlatGeneratedQprimeMassComplexCoordinateDictionary",
                    ],
                    None,
                ),
                (
                    "generated_qprime_mass_complex_coordinate_dictionary_audit",
                    [
                        "lake",
                        "env",
                        "lean",
                        "YangMills/RG/"
                        "BalabanCMP99SourceFlatGeneratedQprimeMassComplexCoordinateDictionaryAudit.lean",
                    ],
                    1,
                ),
            ],
            "RECORDS": [],
        }
    )
    REPRO_PATH.write_text(REPRO_SOURCE, encoding="utf-8", newline="\n")
    return namespace["main"]()


if __name__ == "__main__":
    raise SystemExit(main())
