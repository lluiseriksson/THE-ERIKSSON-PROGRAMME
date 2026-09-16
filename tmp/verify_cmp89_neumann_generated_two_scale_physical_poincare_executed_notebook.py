#!/usr/bin/env python3
"""Fail-closed audit of the executed Colab notebook for the generated
two-scale physical Neumann Poincare producer.

The Colab runtime completed and emitted the evidence/archive hashes, but the
browser tab disappeared after requesting the archive download.  The Drive
notebook retained the complete structured transcript and is the durable object
audited here.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path


EXPECTED_NOTEBOOK_SHA256 = (
    "6cd1cdadfe6d04b20f021de9acc565db1a25a912f284035f90dc222592b0f165"
)
EXPECTED_RUNNER_COMMIT = "5b3290dc6e90443a30ec3b3a77c1192e2a308ce8"
EXPECTED_RUNNER_SHA256 = (
    "d02a3b9520efbafed3ce4368d1ff20da9a0dc0a504402e95f7f589f79f56488a"
)
EXPECTED_BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)
EXPECTED_SOURCE = "774112fb02778c084f846b7e6fbf4fdd9d0af904"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)
EXPECTED_EVIDENCE_SHA256 = (
    "082efff7e4a260115713889b37a0571b40ba5aad7be36e6008fcfeb2d7ef7808"
)
EXPECTED_ARCHIVE_SHA256 = (
    "ef83ac9ff62200a071278f4a278ae17e6a01a94b5ee07118952b5ab249814f18"
)
EXPECTED_STAGES = [
    "download_toolchain",
    "apt_update",
    "install_zstd",
    "extract_toolchain",
    "lean_version",
    "lake_version",
    "clone",
    "checkout",
    "head",
    "overlay_text_guard",
    "import_prefix_guard",
    "lake_update",
    "mathlib_pin",
    "cache_get",
    "generated_two_scale_physical_poincare_focal",
    "generated_two_scale_physical_poincare_audit",
]
EXPECTED_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannGeneratedTwoScalePhysicalPoincare.lean":
        "c27e87488682b6d34445af8fd92b2d67a19e74d1e5eb89b21c6eaf767b2936d1",
    "YangMills/RG/BalabanCMP89SourceNeumannGeneratedTwoScalePhysicalPoincareAudit.lean":
        "3a52036a09c3e639c87a64441d349f3dfcf06e4216dc88da19f8e9b23fe2356f",
}
EXPECTED_AXIOMS = {
    "YangMills.RG.cmp89SourceNeumann_generatedTwoScale_quantitativePoincare_of_physical_feedback",
    "YangMills.RG.exists_pos_cmp89SourceNeumann_generatedTwoScale_physicalPoincare_radius",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main() -> None:
    require(len(sys.argv) == 2, "usage: verifier EXECUTED_NOTEBOOK.ipynb")
    path = Path(sys.argv[1])
    raw = path.read_bytes()
    measured = hashlib.sha256(raw).hexdigest()
    require(measured == EXPECTED_NOTEBOOK_SHA256,
            f"NOTEBOOK_HASH_MISMATCH expected={EXPECTED_NOTEBOOK_SHA256} measured={measured}")

    notebook = json.loads(raw.decode("utf-8"))
    require(len(notebook.get("cells", [])) == 1, "NOTEBOOK_CELL_COUNT_MISMATCH")
    cell = notebook["cells"][0]
    source = "".join(cell.get("source", []))
    outputs = cell.get("outputs", [])
    transcript = "".join(
        "".join(output.get("text", []))
        for output in outputs
        if output.get("output_type") == "stream"
    )

    runner_url = (
        "https://raw.githubusercontent.com/lluiseriksson/"
        f"THE-ERIKSSON-PROGRAMME/{EXPECTED_RUNNER_COMMIT}/scripts/"
        "colab_cmp89_neumann_generated_two_scale_physical_poincare_cold.py"
    )
    require(source.count(runner_url) == 1, "RUNNER_URL_NOT_UNIQUE")
    require(source.count(EXPECTED_RUNNER_SHA256) == 1, "RUNNER_HASH_NOT_UNIQUE")
    require(transcript.count(f"RUNNER_TRANSPORT_SHA256={EXPECTED_RUNNER_SHA256}") == 1,
            "RUNNER_TRANSPORT_GATE_MISSING")
    require(transcript.count(f"BASE_RUNNER_TRANSPORT_SHA256={EXPECTED_BASE_RUNNER_SHA256}") == 1,
            "BASE_RUNNER_GATE_MISSING")
    require("RUNNER_REV=cmp89-neumann-generated-two-scale-physical-poincare-cold-v1" in transcript,
            "RUNNER_REV_MISSING")
    require("RUNTIME=CPU RAM_GIB=50.99" in transcript, "HIGH_RAM_CPU_RUNTIME_MISSING")
    require(f"HEAD is now at {EXPECTED_SOURCE[:8]}" in transcript, "CHECKOUT_LINE_MISSING")
    require(f"\n{EXPECTED_SOURCE}\n" in transcript, "EXACT_HEAD_MISSING")
    require(f"\n{EXPECTED_MATHLIB}\n" in transcript, "MATHLIB_PIN_MISSING")
    require(f"TOOLCHAIN_ASSET_SHA256={EXPECTED_TOOLCHAIN}" in transcript,
            "TOOLCHAIN_HASH_MISSING")

    for blob, digest in EXPECTED_BLOBS.items():
        require(f"SOURCE_BLOB={blob} SHA256={digest}" in transcript,
                f"SOURCE_BLOB_GATE_MISSING={blob}")

    records = re.findall(r"^STAGE=([^ ]+) EXIT=([0-9]+) SECONDS=([0-9.]+)$",
                         transcript, flags=re.MULTILINE)
    require([stage for stage, _, _ in records] == EXPECTED_STAGES,
            "STAGE_ORDER_OR_COUNT_MISMATCH=" + repr(records))
    require(all(exit_code == "0" for _, exit_code, _ in records),
            "NONZERO_STAGE_EXIT")
    require("Build completed successfully (8723 jobs)." in transcript,
            "FOCAL_JOB_COUNT_MISSING")

    axiom_lines = re.findall(
        r"^AXIOM_GATE=([^ ]+) AXIOMS=([^\n]+)$", transcript, flags=re.MULTILINE
    )
    require({name for name, _ in axiom_lines} == EXPECTED_AXIOMS,
            "AXIOM_DECLARATION_SET_MISMATCH=" + repr(axiom_lines))
    for name, axioms in axiom_lines:
        require(axioms == "Classical.choice,Quot.sound,propext",
                f"AXIOM_SET_MISMATCH declaration={name} axioms={axioms}")
    require("sorryAx" not in transcript and "ofReduceBool" not in transcript,
            "FORBIDDEN_AXIOM_NAME_PRESENT")

    require(f"EVIDENCE_SHA256={EXPECTED_EVIDENCE_SHA256}" in transcript,
            "EVIDENCE_HASH_MISSING")
    require(f"EVIDENCE_ARCHIVE_SHA256={EXPECTED_ARCHIVE_SHA256}" in transcript,
            "ARCHIVE_HASH_MISSING")
    require(transcript.count("FINAL_STATUS=PASS") == 1, "FINAL_PASS_NOT_UNIQUE")
    require("FINAL_STATUS=FAIL" not in transcript, "FINAL_FAIL_PRESENT")
    require("EVIDENCE_DOWNLOAD_REQUESTED=1" in transcript,
            "DOWNLOAD_REQUEST_MARKER_MISSING")

    print("CMP89_NEUMANN_GENERATED_TWO_SCALE_PHYSICAL_POINCARE_EXECUTED_NOTEBOOK_OK")
    print(f"NOTEBOOK_SHA256={measured.upper()}")
    print(f"TRANSCRIPT_CHARS={len(transcript)}")
    print(f"STAGE_COUNT={len(records)}")
    print(f"FOCAL_SECONDS={records[-2][2]}")
    print(f"AUDIT_SECONDS={records[-1][2]}")
    print(f"EMITTED_EVIDENCE_SHA256={EXPECTED_EVIDENCE_SHA256.upper()}")
    print(f"EMITTED_ARCHIVE_SHA256={EXPECTED_ARCHIVE_SHA256.upper()}")


if __name__ == "__main__":
    main()
