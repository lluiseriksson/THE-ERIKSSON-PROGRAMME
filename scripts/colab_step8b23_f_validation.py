#!/usr/bin/env python3
"""Colab gate for Step 8b.23 Unit F over sealed A--E prerequisites.

This validates periodic owner decay only.  Regional B0, the independent-scale
dictionary, window 15, terminal fields and TermSource remain open.
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
spec = importlib.util.spec_from_file_location("step8b23_f_base_runner", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "step8b23-f-v1"
runner.SOURCE_SHA = 'ac32b03d824bb341fa21c31006ffbecf8e660bac'
runner.ROOT = Path("/content/hrpoly-step8b23-f")
runner.EVIDENCE = Path("/content/hrpoly-step8b23-f-evidence")
runner.ARCHIVE = Path("/content/hrpoly-step8b23-f-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-step8b23-f-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMills/RG/BalabanCMP89CenteredBrillouinAffineSlice.lean': '7887b8583da2f189ac0af22a39f3f401300612c35149571553cff2135b75fbf4',
    'YangMills/RG/BalabanCMP89CenteredBrillouinAffineSliceAudit.lean': '2d22ba868fcd5c3262a105163aea87b159f3215dd6acb63920a041e3ddae5adb',
    'YangMills/RG/BalabanCMP89CenteredUnitCubeTorusQuotient.lean': 'a02095bfd4ae48fa3ea583ebf472af4e1a1d54ed61a8f07f4f9290278d083624',
    'YangMills/RG/BalabanCMP89CenteredUnitCubeTorusQuotientAudit.lean': 'c475e75ea70836d9a31f993935a3cbef0ba099ec3daf3bd17bea0268b0bc86bd',
    'YangMills/RG/BalabanCMP89CenteredTorusFourierPhase.lean': 'ac0b42198859f258966c22bd480dcb4d3d7762aa6692256f261626ecce2aa412',
    'YangMills/RG/BalabanCMP89CenteredTorusFourierPhaseAudit.lean': '438c63d9d86fff3f4dda819340624dfb71003a9d2111eba2a088153b34262c76',
    'YangMills/RG/BalabanCMP89NormalizedBrillouinToTorusMeasure.lean': '445d2a8ed04f2d86da8ff733ecbea592fc8e570c429655a2c8d95937b531528b',
    'YangMills/RG/BalabanCMP89NormalizedBrillouinToTorusMeasureAudit.lean': 'b3613418139528c719c2bd92541aaddddc14bc7758e012093c7e4c6abe511166',
    'YangMills/RG/BalabanCMP89Eq248GreenMassUniformHolomorphy.lean': 'b5661f61903649b7e3abdcec12be706b432b776ea681c0cd979301bb21253fc2',
    'YangMills/RG/BalabanCMP89Eq248GreenMassUniformHolomorphyAudit.lean': '3d6ac7652107884440ab52a62b6001ce14a09eb1af0d5400c86ade6589821da5',
    'YangMills/RG/BalabanCMP89Eq248DisplayedGreenVectorPeriodicity.lean': 'c125de163a1552ed147af15e9ea1f2d3ce91bd9d8c47b7b7d29e119ca0b28b9a',
    'YangMills/RG/BalabanCMP89Eq248DisplayedGreenVectorPeriodicityAudit.lean': 'c84daddc3aaa44781215c70644e1aeb70ed8321ff7ddca1a1dda0d8462542707',
    'YangMills/RG/BalabanCMP89Eq248CenteredGreenTorus.lean': 'b977cda3eacd42021bbbabf478215fc0a6796c97ee0542a0fec434c9fc345a3a',
    'YangMills/RG/BalabanCMP89Eq248CenteredGreenTorusAudit.lean': 'fb56db8b81c30d7e597a2eea97970581179861e668a7dcb7604174de7323a095',
    'YangMills/RG/BalabanCMP99CenteredTorusSampleDictionary.lean': '845598b8cd9c59c6982f32c8a75869d1f20bd3704fbf62f82a5681cf4613eede',
    'YangMills/RG/BalabanCMP99CenteredTorusSampleDictionaryAudit.lean': '8ee679ef6ff2f8b0bc68daac3b5c097737ef9c05627f35e3fca0d5208b9163da',
    'YangMills/RG/BalabanCMP99CenteredTorusPhysicalGreenSampleTransport.lean': 'a6b4a9cdc8ac1055f95a977659cab4c467c879899228201381eb0fb34bfed034',
    'YangMills/RG/BalabanCMP99CenteredTorusPhysicalGreenSampleTransportAudit.lean': '5a481bb4dde0299290267e52eb80b0fd73ba8fed27fbaf783fb4ca68323a12df',
    'YangMills/RG/BalabanCMP89Eq248GreenOneCoordinateContourShift.lean': '19f30514580d5a902f9d0ff2e30ed89fb37fdeaf6691d8fdbeaf5c0690fa8b58',
    'YangMills/RG/BalabanCMP89Eq248GreenOneCoordinateContourShiftAudit.lean': '6cc569c755593f2ff964c3be38348855a083f1aedd80491578d49e76b557911f',
    'YangMills/RG/BalabanCMP89Eq248GreenProductContourTelescope.lean': '89afec986a4be22907d78ca74c53331998433c7383bb464630eaf806a15d85b7',
    'YangMills/RG/BalabanCMP89Eq248GreenProductContourTelescopeAudit.lean': '6087949f5d2f407ba5d6769bf7dda414165668fcdc73bd99bff938391de23204',
    'YangMills/RG/BalabanCMP89Eq248MassUniformGreenBound.lean': '50941c39098fb2d23f43a9a4d2c6cded84d44503eec8fd1d53c1a1379e43fd83',
    'YangMills/RG/BalabanCMP89Eq248MassUniformGreenBoundAudit.lean': '2824b97d5cf2a681a4e41ad7f4115d38fc8e5ebd7b6861b57b040470c55d00b6',
    'YangMills/RG/BalabanCMP89Eq248MassUniformNormalizedGreenBound.lean': '541c5f02d43021693276002bbeca54c9a07009bf688add0b4d83b5a4d0675dd9',
    'YangMills/RG/BalabanCMP89Eq248MassUniformNormalizedGreenBoundAudit.lean': '25dafc6964de0f6f510833c1d862cfa24fb4cdc5aafa46cd967339e1985a7968',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientPhase.lean': '1d31a20620f2869bc19acc6940b5e97b26c702a844ef108de567f661a7c239e8',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientPhaseAudit.lean': '4df7ee5547f911a6ff37f3764e33066872f23abb5ac8da2df06fa4e5832c0177',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientDictionary.lean': 'dd5934702b4302f04ae6db1dbcd561a3af1c1e6e0bb2f869703b80697c83deb6',
    'YangMills/RG/BalabanCMP89CenteredTorusGreenCoefficientDictionaryAudit.lean': '9db5d57a74f2ae8d14ba42145496a61717af3720a28eda626720f27a9f31d399',
    'YangMills/RG/BalabanCMP89SignedLatticeL1TotalSum.lean': '646fe0732faf20a07930e3f660e6bfb163876053a3ad6a876bbc8eabfee64423',
    'YangMills/RG/BalabanCMP89SignedLatticeL1TotalSumAudit.lean': '61071e4b24d370643e7adc8b5f9f1bb6abb445d42760cf99014c377cb9228ad1',
    'YangMills/RG/BalabanCMP89CenteredGreenFourierSummability.lean': '7cc3609614a35d84fa3e4be9f21d5a4acba07b78cb0f982ca3836b5df58989c4',
    'YangMills/RG/BalabanCMP89CenteredGreenFourierSummabilityAudit.lean': '9289b25dc0e03cbb20ca7b39759cedee6a5a7bdd00128d775e986a0ae0007275',
    'YangMills/RG/BalabanCMP99PhysicalGreenFiniteGridAliasing.lean': '65eef7a599e1ce3822b3addc9c0d3ee96e1acfcfabe04aaa66d3e9d92331bb60',
    'YangMills/RG/BalabanCMP99PhysicalGreenFiniteGridAliasingAudit.lean': 'e262cf2a58d8e841e8145d66a7669aae01bc525f0467fd2228bae236f04f99fe',
    'YangMills/RG/BalabanCMP89CenteredPeriodicL1ResidueSum.lean': '977a5ef2d8ae8c84df18203bfe8028f887969d4ec53bb7046f59f83d2241fa7d',
    'YangMills/RG/BalabanCMP89CenteredPeriodicL1ResidueSumAudit.lean': '5fcd885264820be34de18da6f4c652bf2c258309a57c5fa1aed658055a86c582',
    'YangMills/RG/BalabanCMP99CenteredPeriodicEndpointDictionary.lean': 'e9806025d15be3a163dfb02fb988bb9bac3161b717bf3f4f9b49aec4dcbcd31b',
    'YangMills/RG/BalabanCMP99CenteredPeriodicEndpointDictionaryAudit.lean': 'd10f942b4832b84561a08ef035a6789198cfcd69ebfc24536021f20e0e2e2987',
    'YangMills/RG/BalabanCMP99PhysicalGreenZeroResidueBound.lean': '26a4e937a16262d66bded4c7c8535e795517500e611295ab0841e9b8fd76ba4d',
    'YangMills/RG/BalabanCMP99PhysicalGreenZeroResidueBoundAudit.lean': '81e80e2f370bb2ccb62e8c5185b8517d97c544e2d2a197d26df4ec2e7cf6a006',
    'YangMills/RG/BalabanCMP99DiagonalFiniteGreenOwnerBound.lean': 'f9ffd54f9019426811889c1eedd289bc0f921949dd138462ca486159b7ebe338',
    'YangMills/RG/BalabanCMP99DiagonalFiniteGreenOwnerBoundAudit.lean': '8b990608a2d44ea3013e3633e1d701c366505848434c1fb0c0e85af89653108b',
}
runner.QUEUE = [
    (
        '01_cmp89centeredperiodicl1residuesum_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP89CenteredPeriodicL1ResidueSum'],
        None,
    ),
    (
        '01_cmp89centeredperiodicl1residuesum_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP89CenteredPeriodicL1ResidueSumAudit.lean'],
        17,
    ),
    (
        '02_cmp99centeredperiodicendpointdictionary_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99CenteredPeriodicEndpointDictionary'],
        None,
    ),
    (
        '02_cmp99centeredperiodicendpointdictionary_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99CenteredPeriodicEndpointDictionaryAudit.lean'],
        23,
    ),
    (
        '03_cmp99physicalgreenzeroresiduebound_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99PhysicalGreenZeroResidueBound'],
        None,
    ),
    (
        '03_cmp99physicalgreenzeroresiduebound_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99PhysicalGreenZeroResidueBoundAudit.lean'],
        3,
    ),
    (
        '04_cmp99diagonalfinitegreenownerbound_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99DiagonalFiniteGreenOwnerBound'],
        None,
    ),
    (
        '04_cmp99diagonalfinitegreenownerbound_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99DiagonalFiniteGreenOwnerBoundAudit.lean'],
        6,
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
    raise SystemExit(runner.main())
