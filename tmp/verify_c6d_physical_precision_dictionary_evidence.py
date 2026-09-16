#!/usr/bin/env python3
"""Fail-closed verifier specialization for the C6d physical dictionary."""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"
SOURCE_SHA = "deeabe2074d571c62d9229e56eecc6242fa6ad1f"
RUNNER_REV = "c6d-physical-precision-dictionary-v1"
SOURCE_BLOBS_COUNT = 9
SOURCE_BLOBS_SHA256 = "9408EB115001ABC0B529E31D0DE683C3286C1E4D7F2951AF64A00672B7DBAF96"
NOTEBOOK_CELL_SOURCE_SHA256 = "DF736416095070312E44819FDDC660D29F83C20E3F37D72DC65A71F4BB801CD7"
SUCCESS_SENTINEL = "C6D_PHYSICAL_PRECISION_DICTIONARY_EVIDENCE_OK"
MODULES = ['FinitePiLpTypedKernelReindexRectangularAlgebra', 'BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground', 'BalabanCMP99Eq360C6dSourceSeparatedPhysicalLaplacianDictionary', 'BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionary']
AUDIT_STAGES = {'FinitePiLpTypedKernelReindexRectangularAlgebra': '01_finitepilptypedkernelreindexrectangularalgebra_audit', 'BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground': '02_cmp99eq360c6dsourceseparatedphysicalbackground_audit', 'BalabanCMP99Eq360C6dSourceSeparatedPhysicalLaplacianDictionary': '03_cmp99eq360c6dsourceseparatedphysicallaplaciandictionary_audit', 'BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionary': '04_cmp99eq360c6dsourceseparatedphysicalprecisiondictionary_audit'}
EXPECTED_AXIOM_HEADERS = {'FinitePiLpTypedKernelReindexRectangularAlgebra': 3, 'BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground': 3, 'BalabanCMP99Eq360C6dSourceSeparatedPhysicalLaplacianDictionary': 3, 'BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionary': 1}
QUEUE_STAGES = ['01_finitepilptypedkernelreindexrectangularalgebra_focal', '01_finitepilptypedkernelreindexrectangularalgebra_audit', '02_cmp99eq360c6dsourceseparatedphysicalbackground_focal', '02_cmp99eq360c6dsourceseparatedphysicalbackground_audit', '03_cmp99eq360c6dsourceseparatedphysicallaplaciandictionary_focal', '03_cmp99eq360c6dsourceseparatedphysicallaplaciandictionary_audit', '04_cmp99eq360c6dsourceseparatedphysicalprecisiondictionary_focal', '04_cmp99eq360c6dsourceseparatedphysicalprecisiondictionary_audit', '05_c6d_physical_precision_dictionary_yang_mills_core_root']


def load_base():
    spec = importlib.util.spec_from_file_location("c6d_physical_dictionary_evidence_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_PHYSICAL_DICTIONARY_VERIFIER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    base = load_base()
    base.SOURCE_SHA = SOURCE_SHA
    base.RUNNER_REV = RUNNER_REV
    base.SOURCE_BLOBS_COUNT = SOURCE_BLOBS_COUNT
    base.SOURCE_BLOBS_SHA256 = SOURCE_BLOBS_SHA256
    base.NOTEBOOK_CELL_SOURCE_SHA256 = NOTEBOOK_CELL_SOURCE_SHA256
    base.SUCCESS_SENTINEL = SUCCESS_SENTINEL
    base.MODULES = MODULES
    base.AUDIT_STAGES = AUDIT_STAGES
    base.EXPECTED_AXIOM_HEADERS = EXPECTED_AXIOM_HEADERS
    base.QUEUE_STAGES = QUEUE_STAGES
    return base.main()


if __name__ == "__main__":
    raise SystemExit(main())
