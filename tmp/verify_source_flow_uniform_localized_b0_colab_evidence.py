#!/usr/bin/env python3
"""Fail-closed verifier for the uniform/localized source-flow B0 Colab gate."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"
SOURCE_SHA = "73bb1a2008c557840a91e50d8abe6b874947f7ee"
RUNNER_REV = "source-flow-uniform-point-source-b0-v4"
SOURCE_BLOBS_COUNT = 4
SOURCE_BLOBS_SHA256 = "89E64A27501904B7D238A11474C95009704DF735908E6D0735C8DD241C84DC71"
NOTEBOOK_CELL_SOURCE_SHA256 = "C863D38A055B1BB5326B677F6316D31783BA286727744885C01ADBF1D18B0273"
RUNNER_TRANSPORT_SHA256 = "3A6EA0184CCA80E75E59F4F8EF395D65445A796C15B9842AB570BD1D29B971EE"
SUCCESS_SENTINEL = "SOURCE_FLOW_UNIFORM_LOCALIZED_B0_COLAB_EVIDENCE_OK"
MODULES = [
    "BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalUniformPointSourceB0",
    "BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalLocalizedFieldB0",
]
AUDIT_STAGES = {
    MODULES[0]: "source_flow_uniform_point_source_b0_audit",
    MODULES[1]: "source_flow_localized_field_b0_audit",
}
EXPECTED_AXIOM_HEADERS = {MODULES[0]: 5, MODULES[1]: 2}
QUEUE_STAGES = [
    "source_flow_uniform_point_source_b0_focal",
    "source_flow_uniform_point_source_b0_audit",
    "source_flow_localized_field_b0_focal",
    "source_flow_localized_field_b0_audit",
]


def load_base():
    spec = importlib.util.spec_from_file_location("uniform_b0_evidence_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("UNIFORM_B0_VERIFIER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def executed_notebook_text(path: Path) -> str:
    if not path.is_file():
        raise RuntimeError(f"NOTEBOOK_NOT_FOUND={path}")
    notebook = json.loads(path.read_text(encoding="utf-8"))
    cells = notebook.get("cells")
    if not isinstance(cells, list):
        raise RuntimeError("NOTEBOOK_CELLS_NOT_LIST")
    code_cells = [cell for cell in cells if cell.get("cell_type") == "code"]
    if len(code_cells) != 1:
        raise RuntimeError(f"NOTEBOOK_CODE_CELL_COUNT={len(code_cells)}")
    cell = code_cells[0]
    source = cell.get("source")
    if isinstance(source, list):
        source_text = "".join(source)
    elif isinstance(source, str):
        source_text = source
    else:
        raise RuntimeError("NOTEBOOK_CELL_SOURCE_INVALID")
    source_sha = hashlib.sha256(source_text.encode()).hexdigest().upper()
    if source_sha != NOTEBOOK_CELL_SOURCE_SHA256:
        raise RuntimeError(
            f"NOTEBOOK_CELL_SOURCE_SHA256={source_sha} "
            f"EXPECTED={NOTEBOOK_CELL_SOURCE_SHA256}"
        )
    if cell.get("execution_count") is None:
        raise RuntimeError("NOTEBOOK_CELL_NOT_EXECUTED")
    chunks: list[str] = []
    for index, output in enumerate(cell.get("outputs", [])):
        output_type = output.get("output_type")
        if output_type == "stream":
            text = output.get("text")
            if isinstance(text, list):
                chunks.append("".join(text))
            elif isinstance(text, str):
                chunks.append(text)
            else:
                raise RuntimeError(f"NOTEBOOK_STREAM_TEXT_{index}_INVALID")
        elif output_type == "error":
            if output.get("ename") != "SystemExit" or str(output.get("evalue")) != "0":
                raise RuntimeError(f"NOTEBOOK_ERROR_OUTPUT_{index}={output!r}")
        elif output_type not in {"display_data", "execute_result"}:
            raise RuntimeError(f"NOTEBOOK_OUTPUT_TYPE_{index}={output_type!r}")
    result = "".join(chunks)
    required = (
        "FINAL_STATUS=PASS",
        f"RUNNER_TRANSPORT_SHA256={RUNNER_TRANSPORT_SHA256.lower()}",
        "EVIDENCE_DOWNLOAD_REQUESTED=1",
        "RUNTIME_RETAINED_FOR_EVIDENCE_DOWNLOAD=1",
    )
    for token in required:
        if result.count(token) != 1:
            raise RuntimeError(
                f"NOTEBOOK_TOKEN_COUNT_{token}={result.count(token)} EXPECTED=1"
            )
    for forbidden in ("FINAL_STATUS=FAIL", "sorryAx", "ofReduceBool"):
        if forbidden in result:
            raise RuntimeError(f"NOTEBOOK_FORBIDDEN_TOKEN={forbidden}")
    return result


def main() -> int:
    base = load_base()
    base.SOURCE_SHA = SOURCE_SHA
    base.RUNNER_REV = RUNNER_REV
    base.SOURCE_BLOBS_COUNT = SOURCE_BLOBS_COUNT
    base.SOURCE_BLOBS_SHA256 = SOURCE_BLOBS_SHA256
    base.SUCCESS_SENTINEL = SUCCESS_SENTINEL
    base.MODULES = MODULES
    base.AUDIT_STAGES = AUDIT_STAGES
    base.EXPECTED_AXIOM_HEADERS = EXPECTED_AXIOM_HEADERS
    base.QUEUE_STAGES = QUEUE_STAGES
    base.executed_notebook_text = executed_notebook_text
    return base.main()


if __name__ == "__main__":
    raise SystemExit(main())
