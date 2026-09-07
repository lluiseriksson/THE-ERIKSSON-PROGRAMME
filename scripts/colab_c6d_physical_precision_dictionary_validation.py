#!/usr/bin/env python3
"""Fresh Colab gate for the C6d physical precision dictionary.

This runner validates rectangular kernel reindexing, the exact Step-7b
physical background, the covariant D0/Laplacian transport and the literal
source-gauge precision equality. It checks ten public axiom readouts and
every repository consumer through ``YangMillsCore``. Passing closes only
the named C6d physical precision dictionary: it does not prove Green
decay, the four actions, uniform B0/delta0, window 15, ``20/41`` or
``TermSource``.
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

runner.RUNNER_REV = "c6d-physical-precision-dictionary-v1"
runner.SOURCE_SHA = 'deeabe2074d571c62d9229e56eecc6242fa6ad1f'
runner.ROOT = Path("/content/hrpoly-c6d-physical-precision-dictionary")
runner.EVIDENCE = Path("/content/hrpoly-c6d-physical-precision-dictionary-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-c6d-physical-precision-dictionary-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-c6d-physical-precision-dictionary-paths.txt"
)
runner.SOURCE_BLOBS = {
    'YangMills/RG/FinitePiLpTypedKernelReindexRectangularAlgebra.lean': 'ffab3209ed011ec82472901c99562384d0d76dec38b0eba7fd462e783af19cfe',
    'YangMills/RG/FinitePiLpTypedKernelReindexRectangularAlgebraAudit.lean': '8df9ad648e5ef2be1316ee96e15afcaf6ab0e1c0591475ab6e82d415fe38a35f',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground.lean': 'a0946be86e0b64d79809bc4e062101349ab4891201d3f470be30e36b81f34e9a',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackgroundAudit.lean': '757c565a1bec551d0bd804f216cc1173a00bad19847f4e51921fc88e8f8f5fe6',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLaplacianDictionary.lean': 'ed23cd945eacefc09b4048a4dd41a8dac1160578ba69a64a94d73605bb65c5f9',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLaplacianDictionaryAudit.lean': 'ccfacf337675cbac6ee797e00930100f53518278eaf326117869272ba3b4e607',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionary.lean': 'c60d7a000dba0c3413744c16b6de882b3b5b20face89b59340e9eb4337096f83',
    'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionaryAudit.lean': '12eb0e0bfec057255852ea548343c0782b36b44118cbc5e869bab01c7f909039',
    'YangMillsCore.lean': 'f03c1b3fbbe10c90412ef675f42f33e35912440e0fcbe6a8e20d2cb1d287d9c1',
}
runner.QUEUE = [
    (
        '01_finitepilptypedkernelreindexrectangularalgebra_focal',
        ['lake', 'build', 'YangMills.RG.FinitePiLpTypedKernelReindexRectangularAlgebra'],
        None,
    ),
    (
        '01_finitepilptypedkernelreindexrectangularalgebra_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/FinitePiLpTypedKernelReindexRectangularAlgebraAudit.lean'],
        3,
    ),
    (
        '02_cmp99eq360c6dsourceseparatedphysicalbackground_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground'],
        None,
    ),
    (
        '02_cmp99eq360c6dsourceseparatedphysicalbackground_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackgroundAudit.lean'],
        3,
    ),
    (
        '03_cmp99eq360c6dsourceseparatedphysicallaplaciandictionary_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedPhysicalLaplacianDictionary'],
        None,
    ),
    (
        '03_cmp99eq360c6dsourceseparatedphysicallaplaciandictionary_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLaplacianDictionaryAudit.lean'],
        3,
    ),
    (
        '04_cmp99eq360c6dsourceseparatedphysicalprecisiondictionary_focal',
        ['lake', 'build', 'YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionary'],
        None,
    ),
    (
        '04_cmp99eq360c6dsourceseparatedphysicalprecisiondictionary_audit',
        ['lake', 'env', 'lean', 'YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionaryAudit.lean'],
        1,
    ),
    (
        '05_c6d_physical_precision_dictionary_yang_mills_core_root',
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
