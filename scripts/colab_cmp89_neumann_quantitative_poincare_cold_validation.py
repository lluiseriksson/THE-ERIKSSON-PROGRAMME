#!/usr/bin/env python3
"""Fresh Colab seal for the quantitative CMP89 Neumann Poincare chain."""

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
    "cmp89_neumann_quantitative_poincare_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_BY_GATE = {
    201: {
        "YangMills.RG.cmp89SourceNeumannOneStepDefectCoefficient",
        "YangMills.RG.norm_cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_sq_le",
        "YangMills.RG.eq_zero_of_cmp89SourceNeumann_oneStep_absorption",
    },
    202: {
        "YangMills.RG.cmp89SourceNeumannInternalBlockEnergy_nonneg",
        "YangMills.RG.norm_covariantEdgeDefect_sq_le_neumannInternalBlockEnergy",
        "YangMills.RG.covariantPathEnergy_le_length_mul_neumannInternalBlockEnergy",
    },
    203: {
        "YangMills.RG.norm_cmp99BlockContainedContour_defect_sq_le_neumannInternalBlockEnergy",
        "YangMills.RG.sum_norm_cmp99BlockContainedContour_defect_sq_le_neumann",
        "YangMills.RG.sum_norm_sq_active_block_le_neumannEnergy_add_average",
    },
    204: {
        "YangMills.RG.sum_cmp89SourceNeumannInternalBlockEnergy_le_raw_norm_sq",
        "YangMills.RG.norm_cmp89SourceNeumannRegionalRawD0_sq_eq_spacing_sq_mul",
        "YangMills.RG.cmp89SourceNeumannOneScalePoincareConstant_pos",
        "YangMills.RG.norm_sq_le_cmp89SourceNeumannOneScalePoincare",
        "YangMills.RG.cmp89SourceNeumann_oneScale_quantitativePoincare",
    },
    205: {
        "YangMills.RG.cmp89SourceNeumannOneStepDefectCoefficient_physical_scaling",
        "YangMills.RG.cmp89SourceNeumannOneScalePoincare_mul_defect_physical_scaling",
        "YangMills.RG.cmp89SourceNeumannOneScalePoincare_mul_defect_lt_one_iff",
    },
}


def parse_axioms_exact(output: str, gate: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    expected = EXPECTED_BY_GATE[gate]
    if set(found) != expected:
        raise RuntimeError(
            "AXIOM_DECLARATIONS_MISMATCH="
            + repr({"found": sorted(found), "expected": sorted(expected)})
        )
    for name in sorted(expected):
        axioms = {item for item in found[name].split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp89-neumann-quantitative-poincare-cold-v1"
runner.SOURCE_SHA = "3982806d4e542957e70ff4418d2bf43601555c0f"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-quantitative-poincare-cold")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-neumann-quantitative-poincare-cold-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-neumann-quantitative-poincare-cold-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-neumann-quantitative-poincare-cold-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannRecursiveAbsorptionStep.lean":
        "55edb0d1abae970e1c64eea099d9a702e0a1b8d0ee4c2967c2a355dd50e5c0f8",
    "YangMills/RG/BalabanCMP89SourceNeumannRecursiveAbsorptionStepAudit.lean":
        "8180570c48cfdf703f60bd4ab6ed67bc3b36e3d73bf976ed94ba55950f606ea8",
    "YangMills/RG/BalabanCMP89SourceNeumannInternalBlockEnergy.lean":
        "2313898cec0e9d2b8f4cd641a6a8978baae1bc2963a4820108edf4fc3104e073",
    "YangMills/RG/BalabanCMP89SourceNeumannInternalBlockEnergyAudit.lean":
        "c997a94ee5aa21e2270f7536fd5cef1343760615bc187d7367e654f61f8d5481",
    "YangMills/RG/BalabanCMP89SourceNeumannInternalBlockPoincare.lean":
        "aef04eab49ddde0f7bd79a12019c640f88ec554c8894f7d5938792d2cea0dffa",
    "YangMills/RG/BalabanCMP89SourceNeumannInternalBlockPoincareAudit.lean":
        "92ee18cade0091792d0128a65d7908bae846989efb50b6ba210c6a99863f3f6c",
    "YangMills/RG/BalabanCMP89SourceNeumannQuantitativeOneScalePoincare.lean":
        "5a30900c14c7db762f09d6127a2df6fc7821a9fd78fde83e5077def2a3be5a49",
    "YangMills/RG/BalabanCMP89SourceNeumannQuantitativeOneScalePoincareAudit.lean":
        "3ad1392bb93250f44b40dbdf2feab36ee25570ceab55a29bde67dfb2701e155f",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalOneStepScaling.lean":
        "814c7b1e5258196fe76dd48381f2962f52d2958b8b3d97e4d297df58bedd446b",
    "YangMills/RG/BalabanCMP89SourceNeumannPhysicalOneStepScalingAudit.lean":
        "167a36ddafefcfcdd4791e17874eef013179b751d37e0bf8a415c07608e53042",
}
runner.QUEUE = [
    ("recursive_absorption_step_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannRecursiveAbsorptionStep"], None),
    ("recursive_absorption_step_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannRecursiveAbsorptionStepAudit.lean"], 201),
    ("internal_block_energy_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannInternalBlockEnergy"], None),
    ("internal_block_energy_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannInternalBlockEnergyAudit.lean"], 202),
    ("internal_block_poincare_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannInternalBlockPoincare"], None),
    ("internal_block_poincare_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannInternalBlockPoincareAudit.lean"], 203),
    ("quantitative_one_scale_poincare_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannQuantitativeOneScalePoincare"], None),
    ("quantitative_one_scale_poincare_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannQuantitativeOneScalePoincareAudit.lean"], 204),
    ("physical_one_step_scaling_focal", ["lake", "build",
      "YangMills.RG.BalabanCMP89SourceNeumannPhysicalOneStepScaling"], None),
    ("physical_one_step_scaling_audit", ["lake", "env", "lean",
      "YangMills/RG/BalabanCMP89SourceNeumannPhysicalOneStepScalingAudit.lean"], 205),
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
