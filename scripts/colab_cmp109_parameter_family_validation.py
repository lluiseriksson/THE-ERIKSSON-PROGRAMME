#!/usr/bin/env python3
"""Fresh-Colab validation of the parameter-uniform CMP109 Banach brick."""

from __future__ import annotations

from pathlib import Path
import time

import colab_localized_region_index_validation as runner


runner.RUNNER_REV = "cmp109-parameter-family-v1"
runner.SOURCE_SHA = "de7c13a59083c2b2000bb722203f9afd22aaae5d"
runner.TARGET = "YangMills.RG.BalabanCMP109ConstraintCorrectionParameterFamily"
runner.AUDIT_FILE = "CMP109ConstraintCorrectionParameterFamilyValidationAudit.lean"
runner.AXIOM_DECLARATIONS = [
    "YangMills.RG.CMP109ConstraintCorrectionParameterFamilyData.contractionRate_lt_one",
    "YangMills.RG.CMP109ConstraintCorrectionParameterFamilyData.correction_mem_ball",
    "YangMills.RG.CMP109ConstraintCorrectionParameterFamilyData.correction_fixedPoint",
    "YangMills.RG.CMP109ConstraintCorrectionParameterFamilyData.correction_physicalEquation",
]
runner.EXPECTED_AXIOM_LINES = len(runner.AXIOM_DECLARATIONS)
runner.ROOT = Path("/content/hrpoly-cmp109-parameter-family")
runner.EVIDENCE = Path("/content/hrpoly-cmp109-parameter-family-evidence")
runner.TRANSCRIPT = runner.EVIDENCE / "transcript.log"
runner.START = time.perf_counter()
runner.RESULT = {
    "focal_exit": None,
    "audit_exit": None,
    "axiom_lines_seen": 0,
    "axiom_lines_expected": runner.EXPECTED_AXIOM_LINES,
    "axiom_content_ok": None,
}


if __name__ == "__main__":
    runner.main()
