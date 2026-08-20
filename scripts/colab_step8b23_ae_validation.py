#!/usr/bin/env python3
"""Colab gate for Step 8b.23 Units A--E (18 ordered bricks).

The immutable mathematical checkpoint is SOURCE_SHA.  The queue is
stop-on-first-error and audits every focal immediately.  Unit F, regional B0,
window 15, terminal fields and TermSource are outside this runner's scope.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import time
import urllib.request


HERE = Path("/content")
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/bcc852cee5e709bff91fad7de26fa21cff754e1f/scripts/colab_qprime_row_validation.py'
BASE_RUNNER_SHA256 = 'd06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee'
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("step8b23_ae_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "step8b23-ae-v57"
runner.SOURCE_SHA = '36eebd5aa99db0063f22081bda0f58da01359e2f'
runner.ROOT = Path("/content/hrpoly-step8b23-ae")
runner.EVIDENCE = Path("/content/hrpoly-step8b23-ae-evidence")
runner.ARCHIVE = Path("/content/hrpoly-step8b23-ae-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-step8b23-ae-paths.txt")

runner.SOURCE_BLOBS = {
    'YangMills/RG/BalabanCMP89CenteredBrillouinAffineSlice.lean': 'c266423f68421b5ba771140586d458ef53d766831fb06d12a879ce25ae3e9853',
    'YangMills/RG/BalabanCMP89CenteredBrillouinAffineSliceAudit.lean': '0bb147baf82707e0de48a3ce888b968c005d9584b9bae6d14a5d9cac012a23c2',
    'YangMills/RG/BalabanCMP89CenteredUnitCubeTorusQuotient.lean': '1bd9c2c0660a0b7a9eb94e1c7867028ed7c4278210317cbf8cdd674e1d720bc7',
    'YangMills/RG/BalabanCMP89CenteredUnitCubeTorusQuotientAudit.lean': '8a14bdda0ea10e74d3bc59b0ee183aea477490b6acef6880dbc2dca62802bb75',
    'YangMills/RG/BalabanCMP89CenteredTorusFourierPhase.lean': 'b7c58f3becacd65e0c4a1a4387804574eb1c74d0284547c8bf8d09453da03a0c',
    'YangMills/RG/BalabanCMP89CenteredTorusFourierPhaseAudit.lean': '246ef491a33109859d1f4e0a7889eb1f209a2a363e4001717d0e0dc6e67eea88',
    'YangMills/RG/BalabanCMP89NormalizedBrillouinToTorusMeasure.lean': 'f307d1e00de4f1ac64a08639b533c2df2bba2bc558209f877cbc3f04fc916e11',
    'YangMills/RG/BalabanCMP89NormalizedBrillouinToTorusMeasureAudit.lean': '35db023192efabc07380ebf0299eb1c07245be4e16e201e14e11ea5f201b38e8',
    'YangMills/RG/BalabanCMP89Eq248GreenMassUniformHolomorphy.lean': '05ebd095ba003fd2872f09c60cff0c36cd68e7a8ffdd0f55009179cf30729d6b',
    'YangMills/RG/BalabanCMP89Eq248GreenMassUniformHolomorphyAudit.lean': '2510acfc6f38f7c45ee669d93f58795214a6725ccbe9fe9e77dbf52fb5711cec',
    'YangMills/RG/BalabanCMP89Eq248DisplayedGreenVectorPeriodicity.lean': 'b6ed5793f44b3de83f77747a46daccd32f9fe45ba0dd4d466c93a525f6d9c7dc',
    'YangMills/RG/BalabanCMP89Eq248DisplayedGreenVectorPeriodicityAudit.lean': '0ec7924267e39b7712b348902bdd4e69b29cb64ca5ca22dab0d77a128ee1ff2e',
    'YangMills/RG/BalabanCMP89Eq248CenteredGreenTorus.lean': 'e69480f49800acf6d3eb575e2bdf4303590afac5af0dfd57465e5189e222e7a6',
    'YangMills/RG/BalabanCMP89Eq248CenteredGreenTorusAudit.lean': 'e698677b04e71a36f3783b58db1f37e1cb84a89e69b9cb28805e589210f0efc0',
    'YangMills/RG/BalabanCMP99CenteredTorusSampleDictionary.lean': '53785e1695c34c91b750527baded4271d2abe9469109762c7ac08ba2edb4dd4b',
    'YangMills/RG/BalabanCMP99CenteredTorusSampleDictionaryAudit.lean': 'ee9d5c4d19309a5586465d6c650e3602397a2e7372c74da55a6d845d02ad96ce',
    'YangMills/RG/BalabanCMP99CenteredTorusPhysicalGreenSampleTransport.lean': 'cd6a76a96b75fdd79cd67d889ff92b45bef4dfc66b98e6fe831a295986779d61',
    'YangMills/RG/BalabanCMP99CenteredTorusPhysicalGreenSampleTransportAudit.lean': 'ebbc79a2c206e04c9b290c096590a2456cc8eab293bccdcf6db27ccddd3767a8',
    'YangMills/RG/BalabanCMP89Eq248GreenOneCoordinateContourShift.lean': '325588d8280e99f2c45858f045b952064639fc24341afca6f049a485dfd6ba6d',
    'YangMills/RG/BalabanCMP89Eq248GreenOneCoordinateContourShiftAudit.lean': '4a2349c526da39442794b7dc75a30ca5f45ca2b9faf33a5f190e98882aceab60',
    'YangMills/RG/BalabanCMP89Eq248GreenProductContourTelescope.lean': 'cfe37312d6db0cce864e33a9b620f6664e04e52e7947c0cfc5dc3b488186cf3b',
    'YangMills/RG/BalabanCMP89Eq248GreenProductContourTelescopeAudit.lean': '2bf1ecedd087092acdb914e64ba0979d2de654febe36fb69c09f29b4d305f171',
    'YangMills/RG/BalabanCMP89Eq248MassUniformGreenBound.lean': 'a07c32e7d21d165355c0b2f3dde635d2251f04401a8239ff7ff9c17243498a52',
    'YangMills/RG/BalabanCMP89Eq248MassUniformGreenBoundAudit.lean': '83fb7dfc26b7e21800465b0a04d53de838b2b76feda52ed4f14bccff438768ff',
    'YangMills/RG/BalabanCMP89Eq248MassUniformNormalizedGreenBound.lean': 'c365329ba58e7cb69b59a16dae62f32e69bc1c3d8e12cedd3cdd2d7665077781',
    'YangMills/RG/BalabanCMP89Eq248MassUniformNormalizedGreenBoundAudit.lean': '7604d1727e8168662806efc6d82470c953cd42443b02705183bea1980790626b',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientPhase.lean': '9fd51d9136ffa446d414fd36f509576bd03fa4081d695f6cb6bda2b691b44ab4',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientPhaseAudit.lean': '613507fd729af2fdb242eeb9a7414286e9de080c893cf0c4ea87b58096f26908',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientDictionary.lean': '53c005aeb97d187a91f4509c91daf9bf448d9375a948e8528e33def1b42e79ef',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientDictionaryAudit.lean': 'ca78912c3c168b77daeffd69808fc72b84f31ca1db28d51477891a7d56794342',
    'YangMills/RG/BalabanCMP89SignedLatticeL1TotalSum.lean': '8ca777ceb2c7a29b2f9da85b5eb4e5d64e7de692ed3a34cccd923e9061dc06fb',
    'YangMills/RG/BalabanCMP89SignedLatticeL1TotalSumAudit.lean': '80bad23756e1a24508d84bb969cebe2dff18ea72bc938fa24b28ab911fb296fb',
    'YangMills/RG/BalabanCMP89CenteredGreenFourierSummability.lean': '24e692d3a7660bcdc3183ffaa23c3a8b50454db98ce45a7e72e74c4f1e2d975b',
    'YangMills/RG/BalabanCMP89CenteredGreenFourierSummabilityAudit.lean': 'e1ff97694e15ed9d0976b033a933a2d1d45bd87cfe7ae73c4efd930fd38de532',
    'YangMills/RG/BalabanCMP99PhysicalGreenFiniteGridAliasing.lean': '6ee73253a553c064f4e1b5a37f4f59916f086381d2cbf59d2ab245d4dc459750',
    'YangMills/RG/BalabanCMP99PhysicalGreenFiniteGridAliasingAudit.lean': 'f9efec45f5856ccc8a97ea5f0240e43c929a495122e58600d19e5a09cfabd643',
    'tmp/Step8b23AENormalizedMeasureCoeff.repro.lean': 'a77d77600322140c6fa45134b3a3b1c974cea5fba8be2b60b7b069505d2f6403',
    'tmp/Step8b23AENormalizedMeasureFull.repro.lean': 'cb7606a9d7a27fa31ebe0b63a294409ea7f5b8ae3097e2523f8c0c2256f0afa8',
    'tmp/Step8b23AEContinuousAtCompExplicit.repro.lean': '65d3f43bd36eae29d3c4ee742163a4101468481f6a760ffc5c4f7d257b26b1e7',
    'tmp/Step8b23AESignedLatticeL1Repairs.repro.lean': '54039ff4df845395f5ede135488a4cb3a5b8d33815b5d99573637dd8154fee1a',
}


def run_with_persistent_log(
    stage: str,
    command: list[str],
    *,
    cwd: Path | None = None,
) -> str:
    """Run one child and retain its complete combined output in evidence."""
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command,
        cwd=cwd,
        env=os.environ.copy(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    output = child.stdout
    print(output, flush=True)
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    log_name = re.sub(r"[^A-Za-z0-9_.-]+", "_", stage) + ".log"
    log_path = runner.EVIDENCE / log_name
    log_path.write_text(output, encoding="utf-8")
    output_hash = hashlib.sha256(output.encode()).hexdigest()
    if hashlib.sha256(log_path.read_bytes()).hexdigest() != output_hash:
        raise RuntimeError("STAGE_LOG_HASH_MISMATCH=" + stage)
    runner.RECORDS.append(
        {
            "stage": stage,
            "exit": child.returncode,
            "seconds": elapsed,
            "output_sha256": output_hash,
            "log": log_name,
        }
    )
    print(
        "STAGE=" + stage + " EXIT=" + str(child.returncode)
        + " SECONDS=%.3f" % elapsed,
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = run_with_persistent_log


def parse_complete_axiom_headers(output: str, expected: int) -> None:
    """Count both textual forms emitted by ``#print axioms``."""
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    headers = len(blocks) + pure
    if headers != expected:
        raise RuntimeError(
            "AXIOM_HEADER_COUNT=" + str(headers)
            + " EXPECTED=" + str(expected)
            + " NONEMPTY=" + str(len(blocks))
            + " EMPTY=" + str(pure)
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET_{index}={sorted(names)}")


parse_complete_axiom_headers(
    "'Fixture.allowed' depends on axioms: [propext, Quot.sound]\n"
    "'Fixture.pure' does not depend on any axioms\n",
    2,
)
runner.parse_axioms = parse_complete_axiom_headers

runner.QUEUE = [
    (
        '00_normalized_measure_coefficient_repro',
        ["lake", "env", "lean", 'tmp/Step8b23AENormalizedMeasureCoeff.repro.lean'],
        None,
    ),
    (
        '00b_normalized_measure_full_repro',
        ["lake", "env", "lean", 'tmp/Step8b23AENormalizedMeasureFull.repro.lean'],
        None,
    ),
    (
        '00c_continuousat_comp_explicit_repro',
        ["lake", "env", "lean", 'tmp/Step8b23AEContinuousAtCompExplicit.repro.lean'],
        None,
    ),
    (
        '00d_signed_lattice_l1_repairs_repro',
        ["lake", "env", "lean", 'tmp/Step8b23AESignedLatticeL1Repairs.repro.lean'],
        None,
    ),

    (
        '01_cmp89centeredbrillouinaffineslice_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89CenteredBrillouinAffineSlice'],
        None,
    ),
    (
        '01_cmp89centeredbrillouinaffineslice_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89CenteredBrillouinAffineSliceAudit.lean'],
        2,
    ),
    (
        '02_cmp89centeredunitcubetorusquotient_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89CenteredUnitCubeTorusQuotient'],
        None,
    ),
    (
        '02_cmp89centeredunitcubetorusquotient_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89CenteredUnitCubeTorusQuotientAudit.lean'],
        20,
    ),
    (
        '03_cmp89centeredtorusfourierphase_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89CenteredTorusFourierPhase'],
        None,
    ),
    (
        '03_cmp89centeredtorusfourierphase_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89CenteredTorusFourierPhaseAudit.lean'],
        4,
    ),
    (
        '04_cmp89normalizedbrillouintotorusmeasure_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89NormalizedBrillouinToTorusMeasure'],
        None,
    ),
    (
        '04_cmp89normalizedbrillouintotorusmeasure_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89NormalizedBrillouinToTorusMeasureAudit.lean'],
        10,
    ),
    (
        '05_cmp89eq248greenmassuniformholomorphy_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89Eq248GreenMassUniformHolomorphy'],
        None,
    ),
    (
        '05_cmp89eq248greenmassuniformholomorphy_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89Eq248GreenMassUniformHolomorphyAudit.lean'],
        11,
    ),
    (
        '06_cmp89eq248displayedgreenvectorperiodicity_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89Eq248DisplayedGreenVectorPeriodicity'],
        None,
    ),
    (
        '06_cmp89eq248displayedgreenvectorperiodicity_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89Eq248DisplayedGreenVectorPeriodicityAudit.lean'],
        4,
    ),
    (
        '07_cmp89eq248centeredgreentorus_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89Eq248CenteredGreenTorus'],
        None,
    ),
    (
        '07_cmp89eq248centeredgreentorus_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89Eq248CenteredGreenTorusAudit.lean'],
        8,
    ),
    (
        '08_cmp99centeredtorussampledictionary_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99CenteredTorusSampleDictionary'],
        None,
    ),
    (
        '08_cmp99centeredtorussampledictionary_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99CenteredTorusSampleDictionaryAudit.lean'],
        5,
    ),
    (
        '09_cmp99centeredtorusphysicalgreensampletransport_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99CenteredTorusPhysicalGreenSampleTransport'],
        None,
    ),
    (
        '09_cmp99centeredtorusphysicalgreensampletransport_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99CenteredTorusPhysicalGreenSampleTransportAudit.lean'],
        5,
    ),
    (
        '10_cmp89eq248greenonecoordinatecontourshift_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89Eq248GreenOneCoordinateContourShift'],
        None,
    ),
    (
        '10_cmp89eq248greenonecoordinatecontourshift_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89Eq248GreenOneCoordinateContourShiftAudit.lean'],
        1,
    ),
    (
        '11_cmp89eq248greenproductcontourtelescope_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89Eq248GreenProductContourTelescope'],
        None,
    ),
    (
        '11_cmp89eq248greenproductcontourtelescope_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89Eq248GreenProductContourTelescopeAudit.lean'],
        5,
    ),
    (
        '12_cmp89eq248massuniformgreenbound_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89Eq248MassUniformGreenBound'],
        None,
    ),
    (
        '12_cmp89eq248massuniformgreenbound_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89Eq248MassUniformGreenBoundAudit.lean'],
        12,
    ),
    (
        '13_cmp89eq248massuniformnormalizedgreenbound_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89Eq248MassUniformNormalizedGreenBound'],
        None,
    ),
    (
        '13_cmp89eq248massuniformnormalizedgreenbound_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89Eq248MassUniformNormalizedGreenBoundAudit.lean'],
        2,
    ),
    (
        '14_cmp89centeredtorusgreencoefficientphase_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89CenteredTorusGreenCoefficientPhase'],
        None,
    ),
    (
        '14_cmp89centeredtorusgreencoefficientphase_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientPhaseAudit.lean'],
        5,
    ),
    (
        '15_cmp89centeredtorusgreencoefficientdictionary_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89CenteredTorusGreenCoefficientDictionary'],
        None,
    ),
    (
        '15_cmp89centeredtorusgreencoefficientdictionary_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientDictionaryAudit.lean'],
        7,
    ),
    (
        '16_cmp89signedlatticel1totalsum_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89SignedLatticeL1TotalSum'],
        None,
    ),
    (
        '16_cmp89signedlatticel1totalsum_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89SignedLatticeL1TotalSumAudit.lean'],
        13,
    ),
    (
        '17_cmp89centeredgreenfouriersummability_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89CenteredGreenFourierSummability'],
        None,
    ),
    (
        '17_cmp89centeredgreenfouriersummability_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89CenteredGreenFourierSummabilityAudit.lean'],
        5,
    ),
    (
        '18_cmp99physicalgreenfinitegridaliasing_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99PhysicalGreenFiniteGridAliasing'],
        None,
    ),
    (
        '18_cmp99physicalgreenfinitegridaliasing_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99PhysicalGreenFiniteGridAliasingAudit.lean'],
        5,
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
