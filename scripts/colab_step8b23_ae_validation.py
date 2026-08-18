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

runner.RUNNER_REV = "step8b23-ae-v16"
runner.SOURCE_SHA = '4c5abad75ebaa80d0861389047fd22575ee4ab11'
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
    'YangMills/RG/BalabanCMP89NormalizedBrillouinToTorusMeasure.lean': '03d49686a0311c1b1098c14851880ac709ce4f11ea2c83e7949eb9e698ae4c82',
    'YangMills/RG/BalabanCMP89NormalizedBrillouinToTorusMeasureAudit.lean': '35db023192efabc07380ebf0299eb1c07245be4e16e201e14e11ea5f201b38e8',
    'YangMills/RG/BalabanCMP89Eq248GreenMassUniformHolomorphy.lean': '95f3666c7d00e2e80dcad94b863b35c352cf9162e809acf9851078498b38173f',
    'YangMills/RG/BalabanCMP89Eq248GreenMassUniformHolomorphyAudit.lean': '2510acfc6f38f7c45ee669d93f58795214a6725ccbe9fe9e77dbf52fb5711cec',
    'YangMills/RG/BalabanCMP89Eq248DisplayedGreenVectorPeriodicity.lean': '03846cecab182fa2eea5fba29a104d69838d9f7e2865da112a60a64f995e029b',
    'YangMills/RG/BalabanCMP89Eq248DisplayedGreenVectorPeriodicityAudit.lean': '0ec7924267e39b7712b348902bdd4e69b29cb64ca5ca22dab0d77a128ee1ff2e',
    'YangMills/RG/BalabanCMP89Eq248CenteredGreenTorus.lean': '39c42d4afca80c9df810f9971809eb57be8b70dff8bc11b4a7997e6bd1072933',
    'YangMills/RG/BalabanCMP89Eq248CenteredGreenTorusAudit.lean': 'e698677b04e71a36f3783b58db1f37e1cb84a89e69b9cb28805e589210f0efc0',
    'YangMills/RG/BalabanCMP99CenteredTorusSampleDictionary.lean': '1dbc344b93891dc2c36ee251a81b70ec3c8e50ea77895851ec7084c2c3735834',
    'YangMills/RG/BalabanCMP99CenteredTorusSampleDictionaryAudit.lean': 'ee9d5c4d19309a5586465d6c650e3602397a2e7372c74da55a6d845d02ad96ce',
    'YangMills/RG/BalabanCMP99CenteredTorusPhysicalGreenSampleTransport.lean': '5ffd9f42d4cbbf35147f78fc5e5198444c4a7186d50e37eda8d453ba0ac05d7e',
    'YangMills/RG/BalabanCMP99CenteredTorusPhysicalGreenSampleTransportAudit.lean': 'ebbc79a2c206e04c9b290c096590a2456cc8eab293bccdcf6db27ccddd3767a8',
    'YangMills/RG/BalabanCMP89Eq248GreenOneCoordinateContourShift.lean': '7c881899c1f70b92854309fcf3debb53e3d3f27ec3e2afdd0dbf9be7167a43e3',
    'YangMills/RG/BalabanCMP89Eq248GreenOneCoordinateContourShiftAudit.lean': '4a2349c526da39442794b7dc75a30ca5f45ca2b9faf33a5f190e98882aceab60',
    'YangMills/RG/BalabanCMP89Eq248GreenProductContourTelescope.lean': '33f013b8d996a584400ad03ffd1878bc5738734f8972707b69d5589ab6fd6d67',
    'YangMills/RG/BalabanCMP89Eq248GreenProductContourTelescopeAudit.lean': '2bf1ecedd087092acdb914e64ba0979d2de654febe36fb69c09f29b4d305f171',
    'YangMills/RG/BalabanCMP89Eq248MassUniformGreenBound.lean': '5637560f3823c5e84833dfdf9d184445aea92c79b78ce56de8b11cb8cc324e8e',
    'YangMills/RG/BalabanCMP89Eq248MassUniformGreenBoundAudit.lean': '83fb7dfc26b7e21800465b0a04d53de838b2b76feda52ed4f14bccff438768ff',
    'YangMills/RG/BalabanCMP89Eq248MassUniformNormalizedGreenBound.lean': '2acecd3d2c9042e9639eb46b0db53a5ed8ede752f66f1574144fb70b28ecf3b9',
    'YangMills/RG/BalabanCMP89Eq248MassUniformNormalizedGreenBoundAudit.lean': '7604d1727e8168662806efc6d82470c953cd42443b02705183bea1980790626b',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientPhase.lean': 'b01992bd7764ac1d91c103ee8befc7734123386dc81069d8ac196c4444e9e941',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientPhaseAudit.lean': '613507fd729af2fdb242eeb9a7414286e9de080c893cf0c4ea87b58096f26908',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientDictionary.lean': '6b20c651c3d9aa3319e010320f8b47de2845c336e59d7f1ae3a2ad32ae784366',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientDictionaryAudit.lean': 'ca78912c3c168b77daeffd69808fc72b84f31ca1db28d51477891a7d56794342',
    'YangMills/RG/BalabanCMP89SignedLatticeL1TotalSum.lean': '2ce03a45c58c74c1be7f8bb5da0e694d3aa048c14c0f18ce3ef95baf423f898b',
    'YangMills/RG/BalabanCMP89SignedLatticeL1TotalSumAudit.lean': '80bad23756e1a24508d84bb969cebe2dff18ea72bc938fa24b28ab911fb296fb',
    'YangMills/RG/BalabanCMP89CenteredGreenFourierSummability.lean': '665f47f30ce334fc25c0ba9100ca82eecae6d32cd278527030d6fb1e4c7d1851',
    'YangMills/RG/BalabanCMP89CenteredGreenFourierSummabilityAudit.lean': 'e1ff97694e15ed9d0976b033a933a2d1d45bd87cfe7ae73c4efd930fd38de532',
    'YangMills/RG/BalabanCMP99PhysicalGreenFiniteGridAliasing.lean': '9d11c7bbb58eb52901cf7be95a0f469832a45e8a0fc04dc812e27a4ae021451e',
    'YangMills/RG/BalabanCMP99PhysicalGreenFiniteGridAliasingAudit.lean': 'f9efec45f5856ccc8a97ea5f0240e43c929a495122e58600d19e5a09cfabd643',
    'tmp/Step8b23AENormalizedMeasureCoeff.repro.lean': 'a77d77600322140c6fa45134b3a3b1c974cea5fba8be2b60b7b069505d2f6403',
    'tmp/Step8b23AENormalizedMeasureFull.repro.lean': '4465da7cd4c9109d3279a5b419ee28c8202a7daf21ed86d556c0018068bce6dd',
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
