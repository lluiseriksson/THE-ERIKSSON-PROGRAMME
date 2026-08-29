#!/usr/bin/env python3
"""Fresh Colab gate for the exact C6d Green owner-value prefix.

This runner validates six positive/zero-depth source/audit pairs from
owner-input action through owner-distance decay and block-localized value,
plus the three reusable literal stencil transports and their three
explicit-terminal-spacing adapters and scalar certificate assembler, the
localized-
coordinate-to-regional-site bridge and the positive- and zero-depth
physical derivative actions completing both four-action prefixes and the
positive- and zero-depth per-scale certificates, all twenty-four public axiom
readouts and every repository consumer through
``YangMillsCore``. Passing remains per-depth: it does not prove uniform
B0/delta0, attain window 15, move ``20/41`` or inhabit ``TermSource``.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
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
spec = importlib.util.spec_from_file_location("c6d_source_green_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def streaming_run(stage, command, cwd=None):
    print("STAGE=" + stage + " CMD=" + repr(command), flush=True)
    started = time.perf_counter()
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    stdout_path = runner.EVIDENCE / (
        f"{len(runner.RECORDS):03d}-{stage}.stdout"
    )
    with stdout_path.open("w", encoding="utf-8", newline="\n") as stream:
        child = subprocess.Popen(
            command,
            cwd=cwd,
            text=True,
            stdout=stream,
            stderr=subprocess.STDOUT,
        )
        next_heartbeat = started + 30
        while True:
            try:
                returncode = child.wait(timeout=1)
                break
            except subprocess.TimeoutExpired:
                now = time.perf_counter()
                if now >= next_heartbeat:
                    stream.flush()
                    print(
                        "STAGE=" + stage + " HEARTBEAT_SECONDS=%.3f"
                        % (now - started),
                        flush=True,
                    )
                    next_heartbeat = now + 30
    elapsed = time.perf_counter() - started
    output = stdout_path.read_text(encoding="utf-8")
    print(output, flush=True)
    runner.RECORDS.append({
        "stage": stage,
        "exit": returncode,
        "seconds": elapsed,
        "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
    })
    print(
        "STAGE=" + stage + " EXIT=" + str(returncode)
        + " SECONDS=%.3f" % elapsed,
        flush=True,
    )
    if returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = streaming_run

runner.RUNNER_REV = "c6d-green-owner-prefix-v1"
runner.SOURCE_SHA = '86d9f0e44a17e6f80667257e4ecfd814a67adaed'
runner.ROOT = Path("/content/hrpoly-c6d-green-owner-prefix")
runner.EVIDENCE = Path("/content/hrpoly-c6d-green-owner-prefix-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-c6d-green-owner-prefix-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-c6d-green-owner-prefix-paths.txt"
)
runner.SOURCE_BLOBS = {
    'YangMills/RG/BalabanCMP99Eq342LeftDerivativeFromValueBound.lean': 'd52f572cf7416dbf06272e53a8595a8e1c6ac19ae28a53e3ed56053a5277032e',
    'YangMills/RG/BalabanCMP99Eq342LeftDerivativeFromValueBoundAudit.lean': '1f8c81ba4707cd1a82f795e93ec8a4fbc13105262baad4d9eb850c960da58f9b',
    'YangMills/RG/BalabanCMP99Eq342RightAdjointFromValueBound.lean': '54b473468f96b55f6dd9a8238cd1833714e43ecd67d49f7d37ec74bd52f3656c',
    'YangMills/RG/BalabanCMP99Eq342RightAdjointFromValueBoundAudit.lean': '2b6cfc00324250e287c18bd13127cd1ca973f9e199d9e718ecee1476444cb952',
    'YangMills/RG/BalabanCMP99Eq342LaplacianFromLeftDerivativeBound.lean': '0961503ef1fe55d977735ecd04afb2c8a359b0a6539a7680102a3aabc72aad08',
    'YangMills/RG/BalabanCMP99Eq342LaplacianFromLeftDerivativeBoundAudit.lean': '297b8b3f4dd035678a60d12656220db96f06250573adbd510b41084da159e5c6',
    'YangMills/RG/BalabanCMP99Eq342LeftDerivativeAtTerminalSpacing.lean': '0091ade313198105e5b12bd989c88a8412fd7ef48c02c88479c102764d7578cf',
    'YangMills/RG/BalabanCMP99Eq342LeftDerivativeAtTerminalSpacingAudit.lean': 'df3a63ac942252d6937919e64bf215eaf1a3655da8968738436c4df533a73a35',
    'YangMills/RG/BalabanCMP99Eq342RightAdjointAtTerminalSpacing.lean': 'd6c0e85515b6e4fadaa6d876ea56e849e43c6cd29a5852c1505d1605fe76697f',
    'YangMills/RG/BalabanCMP99Eq342RightAdjointAtTerminalSpacingAudit.lean': '6ebfcb744b392b033b8fa61f96af8a3360025c66c910957b3be10ea8fb3ec738',
    'YangMills/RG/BalabanCMP99Eq342LaplacianAtTerminalSpacing.lean': 'ec74722387405d0a1b7d155f29c1cd54b23d5ce5cee52767ad90c7882fdeda8a',
    'YangMills/RG/BalabanCMP99Eq342LaplacianAtTerminalSpacingAudit.lean': 'c66ba997261df91aa39d133c4c0e288c1744d39fd2b33aa1422b13f6fcf0d26c',
    'YangMills/RG/BalabanCMP99Eq342SourceLocalizedCertificateAssembler.lean': '76ddd74b69ccea710fcf430c9febefb41948c5c90bacb27368dc2cc6ec0f2890',
    'YangMills/RG/BalabanCMP99Eq342SourceLocalizedCertificateAssemblerAudit.lean': 'cb818fc986c957d00c025c6d557b1af20479f85199be49d73e9c1c2b9c739a00',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputAction.lean': 'f06ee8a851fcdc3370b208f4488b40604d93f3eed4d9c27afca5bf3f44499d7c',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputActionAudit.lean': '4b6e8b8a11f4b334961ffb55b1399c142acdd78dc202f8358303044dfa315462',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputActionZeroDepth.lean': '5fd398dcab7d95dc7e6326d8a6a51be0e5e4dc68830068dd001795484e22b59b',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputActionZeroDepthAudit.lean': '28b280d97c58f9ffe93202fdb39eff4d110a85a5149baa5cf39d65d159a6b159',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecay.lean': 'e0a3150f1e2dd2b6cdc2bf8f74041a7de8fbdb314ddb0c439a19a1b402873bcd',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecayAudit.lean': '690717ad8a208684f6e7aaac53a87654a86d5377a1d9acf2ca48a8d6cf83b84d',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecayZeroDepth.lean': 'd0ed1817a128ef41139e85e39e1b87437620f8aa83407fae567abf5fafd3f6f0',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecayZeroDepthAudit.lean': 'be83694f60544d7e712013b763ae765120d1119a6aa587f0c109bc6bb8852523',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecay.lean': '03eac11132ca9565aac55236a7f6db1046b5f692e13006368c7e369458d4c167',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecayAudit.lean': 'b163b664967bf2e8e3a0982d32f39e1365b625761835f29268fa879136dc243f',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecayZeroDepth.lean': '8d4f7677ec09fe2eb9ced539fe97775cb21f7edf20885087d766789161bc231c',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecayZeroDepthAudit.lean': '64ba4671c1053cf5692a906cb1266cbb6325b2aed1366be8ef3643d803a7b0f3',
    'YangMills/RG/BalabanCMP99SourcePhysicalLocalizedRegionNonempty.lean': '8a0a19722df99ab1d07953176e7ef8f2e6a40b80566d025c46d3f7761d05a2ba',
    'YangMills/RG/BalabanCMP99SourcePhysicalLocalizedRegionNonemptyAudit.lean': '22868aa23a5c54d7f478b7e90b860310af88cb7b2e6e8b37e983c900614e06f5',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLeftDerivative.lean': '44cada353531fe432a1eece7a88a69f81c2792b06b2776e58f0caf739e890e7d',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLeftDerivativeAudit.lean': 'e9dd89b2bbb19a2024d8d8d5576add4b184f2ec10cbd2d937a48f5fb9a21ee49',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenRightAdjoint.lean': '47a351c9559363de8b6f904bcba8983644c723415c7d9ee9c8656d738337b15a',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenRightAdjointAudit.lean': '511f11f803ebca30a1aa8c6920b2a3b57cad07063b30ae8d0397d16ef6e956ab',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLaplacian.lean': '8f428ff5bf107329cfb92c8c048811d911d9a13f1c0643c3f61e5c83383f47c0',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLaplacianAudit.lean': '1d6081e13f1f2997f9eed0d1cd63d5b0e8eade5479b068bbf3c27ccf22169d6a',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthActions.lean': '71c6d7618cd1fcab6757a44ae2e45bc212c8700d5ebc674c9121e4838650f3c8',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthActionsAudit.lean': '766859128a41e2d930935ab70d849981dadb8aac3012a798341c95e613fdcd1f',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenPerDepthCertificate.lean': '3b973f31240e5118db067dd8f3e57128cb58ac7ab34d822ec4e07fe92d4a8d3b',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenPerDepthCertificateAudit.lean': '11b75e297925513364fba75a08bfd986e4d6b4a8e8d8d786ef4cfef6984fecf2',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthCertificate.lean': 'aa4cd444b66fb2c8d094d0d032798d0d1677746a3e2a4e266ef9831a60f56dd7',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthCertificateAudit.lean': 'd252f6213f6dabb1a0403b7ad924f2aed17cd891ea8ff5042819cdb632bd71f6',
    'YangMillsCore.lean': '12fa5fb7dd1eb2bd33be5d5dbc621640ee165f845ab243ed8efa4849044905a0',
}
runner.QUEUE = [
    (
        '01_cmp99eq342leftderivativefromvaluebound_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq342LeftDerivativeFromValueBound'],
        None,
    ),
    (
        '01_cmp99eq342leftderivativefromvaluebound_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq342LeftDerivativeFromValueBoundAudit.lean'],
        1,
    ),
    (
        '02_cmp99eq342rightadjointfromvaluebound_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq342RightAdjointFromValueBound'],
        None,
    ),
    (
        '02_cmp99eq342rightadjointfromvaluebound_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq342RightAdjointFromValueBoundAudit.lean'],
        1,
    ),
    (
        '03_cmp99eq342laplacianfromleftderivativebound_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq342LaplacianFromLeftDerivativeBound'],
        None,
    ),
    (
        '03_cmp99eq342laplacianfromleftderivativebound_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq342LaplacianFromLeftDerivativeBoundAudit.lean'],
        1,
    ),
    (
        '04_cmp99eq342leftderivativeatterminalspacing_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq342LeftDerivativeAtTerminalSpacing'],
        None,
    ),
    (
        '04_cmp99eq342leftderivativeatterminalspacing_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq342LeftDerivativeAtTerminalSpacingAudit.lean'],
        1,
    ),
    (
        '05_cmp99eq342rightadjointatterminalspacing_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq342RightAdjointAtTerminalSpacing'],
        None,
    ),
    (
        '05_cmp99eq342rightadjointatterminalspacing_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq342RightAdjointAtTerminalSpacingAudit.lean'],
        1,
    ),
    (
        '06_cmp99eq342laplacianatterminalspacing_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq342LaplacianAtTerminalSpacing'],
        None,
    ),
    (
        '06_cmp99eq342laplacianatterminalspacing_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq342LaplacianAtTerminalSpacingAudit.lean'],
        1,
    ),
    (
        '07_cmp99eq342sourcelocalizedcertificateassembler_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq342SourceLocalizedCertificateAssembler'],
        None,
    ),
    (
        '07_cmp99eq342sourcelocalizedcertificateassembler_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq342SourceLocalizedCertificateAssemblerAudit.lean'],
        1,
    ),
    (
        '08_cmp99eq360c6dsourceseparatedambientgreenownerinputaction_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputAction'],
        None,
    ),
    (
        '08_cmp99eq360c6dsourceseparatedambientgreenownerinputaction_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputActionAudit.lean'],
        1,
    ),
    (
        '09_cmp99eq360c6dsourceseparatedambientgreenownerinputactionzerodepth_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputActionZeroDepth'],
        None,
    ),
    (
        '09_cmp99eq360c6dsourceseparatedambientgreenownerinputactionzerodepth_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerInputActionZeroDepthAudit.lean'],
        1,
    ),
    (
        '10_cmp99eq360c6dsourceseparatedambientgreenownerdecay_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecay'],
        None,
    ),
    (
        '10_cmp99eq360c6dsourceseparatedambientgreenownerdecay_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecayAudit.lean'],
        1,
    ),
    (
        '11_cmp99eq360c6dsourceseparatedambientgreenownerdecayzerodepth_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecayZeroDepth'],
        None,
    ),
    (
        '11_cmp99eq360c6dsourceseparatedambientgreenownerdecayzerodepth_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenOwnerDecayZeroDepthAudit.lean'],
        1,
    ),
    (
        '12_cmp99eq360c6dsourceseparatedambientgreenblocklocalizedownerdecay_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecay'],
        None,
    ),
    (
        '12_cmp99eq360c6dsourceseparatedambientgreenblocklocalizedownerdecay_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecayAudit.lean'],
        1,
    ),
    (
        '13_cmp99eq360c6dsourceseparatedambientgreenblocklocalizedownerdecayzerodepth_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecayZeroDepth'],
        None,
    ),
    (
        '13_cmp99eq360c6dsourceseparatedambientgreenblocklocalizedownerdecayzerodepth_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecayZeroDepthAudit.lean'],
        1,
    ),
    (
        '14_cmp99sourcephysicallocalizedregionnonempty_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99SourcePhysicalLocalizedRegionNonempty'],
        None,
    ),
    (
        '14_cmp99sourcephysicallocalizedregionnonempty_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99SourcePhysicalLocalizedRegionNonemptyAudit.lean'],
        3,
    ),
    (
        '15_cmp99eq360c6dsourceseparatedambientgreenleftderivative_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLeftDerivative'],
        None,
    ),
    (
        '15_cmp99eq360c6dsourceseparatedambientgreenleftderivative_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLeftDerivativeAudit.lean'],
        1,
    ),
    (
        '16_cmp99eq360c6dsourceseparatedambientgreenrightadjoint_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenRightAdjoint'],
        None,
    ),
    (
        '16_cmp99eq360c6dsourceseparatedambientgreenrightadjoint_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenRightAdjointAudit.lean'],
        1,
    ),
    (
        '17_cmp99eq360c6dsourceseparatedambientgreenlaplacian_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLaplacian'],
        None,
    ),
    (
        '17_cmp99eq360c6dsourceseparatedambientgreenlaplacian_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLaplacianAudit.lean'],
        1,
    ),
    (
        '18_cmp99eq360c6dsourceseparatedambientgreenzerodepthactions_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthActions'],
        None,
    ),
    (
        '18_cmp99eq360c6dsourceseparatedambientgreenzerodepthactions_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthActionsAudit.lean'],
        3,
    ),
    (
        '19_cmp99eq360c6dsourceseparatedambientgreenperdepthcertificate_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenPerDepthCertificate'],
        None,
    ),
    (
        '19_cmp99eq360c6dsourceseparatedambientgreenperdepthcertificate_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenPerDepthCertificateAudit.lean'],
        1,
    ),
    (
        '20_cmp99eq360c6dsourceseparatedambientgreenzerodepthcertificate_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthCertificate'],
        None,
    ),
    (
        '20_cmp99eq360c6dsourceseparatedambientgreenzerodepthcertificate_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenZeroDepthCertificateAudit.lean'],
        1,
    ),
    (
        '21_c6d_green_owner_prefix_yang_mills_core_root',
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
