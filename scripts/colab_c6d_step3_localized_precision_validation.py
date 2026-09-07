#!/usr/bin/env python3
"""Fresh Colab gate for the promoted C6d Step3 localized precision layer.

This runner validates four physical source/audit pairs, all fifteen public
axiom readouts, and every repository consumer through ``YangMillsCore``.  It
does not attain window 15, move ``20/41`` or inhabit ``TermSource``.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
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
spec = importlib.util.spec_from_file_location("c6d_step3_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "c6d-step3-localized-precision-v5"
runner.SOURCE_SHA = '38c4d4df881c99b5fe1a32e97f98563bb1356c0f'
runner.ROOT = Path("/content/hrpoly-c6d-step3-localized-precision")
runner.EVIDENCE = Path("/content/hrpoly-c6d-step3-localized-precision-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-step3-localized-precision-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-step3-localized-precision-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMills/RG/BalabanCMP99Eq335PhysicalLaplacianInternalCarrier.lean': '0dfbf51b7a699f2d9033148d68da895961d6329ca06115ba5f18be7fd6d47914',
    'YangMills/RG/BalabanCMP99Eq335PhysicalLaplacianInternalCarrierAudit.lean': '3cb31294bd0eecaa3191feaf51636582acc799276b3af8a9772904a2cf9218c4',
    'YangMills/RG/BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridge.lean': '621d1abc6b5212492636e8479ece199e12398d10ddf9c7f430705f8967554110',
    'YangMills/RG/BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridgeAudit.lean': 'b5178264197160cbf7382e926f65109657c6c13c5d470388bd781865bf7dfdf5',
    'YangMills/RG/BalabanCMP99SourceLocalizedRetainedTower.lean': 'c0fadde15dd9c0b2785ff7a0e56fafbe0eefaa2ee6679b159cdc829fbea8e0a0',
    'YangMills/RG/BalabanCMP99SourceLocalizedRetainedTowerAudit.lean': '91e25f99a2b175816a71444435f80414d048da5ce15bea4c0cf1c0ce0da2d9bc',
    'YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision.lean': '93edad3cf40610e9bc7d2a4e229644beb09f3cd499e5200aee234f19d78f2e3a',
    'YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecisionAudit.lean': '846b1c97488cdfa48fdf1a350ca229f36c0cace7ff649cf0d50639bb74eb92ce',
    'tmp/C6D-STEP3-LOCALIZED-PRECISION-PATHS.txt': '7543f7686756254763504c5ceb3bfc302dc270c0669f970468df35c9e661dc26',
    'tmp/C6dStep3ContinuousLinearMapEquality.repro.lean': 'ce3e3190800754cd6516a6c5af0b1d165e45374c5c85fa5acf701585050cf81d',
    'YangMillsCore.lean': 'eb460cec95fc88f8f751858b30f39c624d42e7bd266cc5942b8b56b7d6548e08',
}
runner.QUEUE = [
    (
        '00_c6d_step3_clm_extensionality_repro',
        ['lake', 'env', 'lean', 'tmp/C6dStep3ContinuousLinearMapEquality.repro.lean'],
        None,
    ),
    (
        '00a_c6d_step3_axiom_readout_coverage',
        ['python3', 'scripts/check_lean_axiom_readout_coverage.py', '--paths-from', 'tmp/C6D-STEP3-LOCALIZED-PRECISION-PATHS.txt'],
        None,
    ),
    (
        '01_cmp99eq335physicallaplacianinternalcarrier_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq335PhysicalLaplacianInternalCarrier'],
        None,
    ),
    (
        '01_cmp99eq335physicallaplacianinternalcarrier_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq335PhysicalLaplacianInternalCarrierAudit.lean'],
        3,
    ),
    (
        '02_cmp99eq335physicalregularityinternallaplacianbridge_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridge'],
        None,
    ),
    (
        '02_cmp99eq335physicalregularityinternallaplacianbridge_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridgeAudit.lean'],
        2,
    ),
    (
        '03_cmp99sourcelocalizedretainedtower_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99SourceLocalizedRetainedTower'],
        None,
    ),
    (
        '03_cmp99sourcelocalizedretainedtower_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99SourceLocalizedRetainedTowerAudit.lean'],
        4,
    ),
    (
        '04_cmp99eq335physicalregularityclasslocalizedprecision_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision'],
        None,
    ),
    (
        '04_cmp99eq335physicalregularityclasslocalizedprecision_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecisionAudit.lean'],
        6,
    ),
    (
        '05_c6d_step3_yang_mills_core_root',
        ['lake', 'build', 'YangMillsCore'],
        None,
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
