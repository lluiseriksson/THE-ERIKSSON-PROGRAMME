#!/usr/bin/env python3
"""Cold Colab seal for the C6d ambient/compression boundary.

The queue checks eleven promoted source/audit pairs in the exact order fixed
by ``tmp/c6d-ambient-compression-cold-boundary.json`` and then builds
``YangMillsCore`` from the same fresh checkout.  Fifty-eight public
declarations are audited.  This is infrastructure for C6d Step 7b: it does
not attain window 15, move 20/41, or instantiate ``TermSource``.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = "89cb81e0416e6a6fbc66540a8019471bbbcafed5"
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    f"{SOURCE_SHA}/scripts/colab_qprime_row_validation.py"
)
BASE_SHA256 = "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
BASE_PATH = Path("/content/colab_qprime_row_validation.py")

with urllib.request.urlopen(BASE_URL) as response:
    base_source = response.read()
measured = hashlib.sha256(base_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != BASE_SHA256:
    raise RuntimeError("C6D_AMBIENT_COMPRESSION_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location(
    "c6d_ambient_compression_base", BASE_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_AMBIENT_COMPRESSION_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ("BalabanCMP99RegionalDirichletGaugePrecisionCompression", 2),
    ("BalabanCMP99SourceActiveRegionFullCompanion", 5),
    ("BalabanCMP99SourceGeneratedMassCompression", 3),
    ("BalabanCMP99SourceGeneratedPhysicalPrecisionCompression", 3),
    ("BalabanCMP99SourceActiveRegionFullCompanionPrecision", 6),
    ("BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecision", 8),
    ("BalabanCMP99ActiveGaugeRegionReindex", 10),
    ("BalabanCMP99Eq360C6dSourceAmbientBaselinePrecision", 8),
    ("BalabanCMP99ActiveGaugeRegionReindexGreen", 4),
    ("BalabanCMP99SourceActiveRegionFullCompanionZeroDepth", 3),
    ("BalabanCMP99SourceActiveRegionFullCompanionZeroDepthGreen", 6),
]

runner.RUNNER_REV = "c6d-ambient-compression-cold-v2-streaming-heartbeat"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6d-ambient-compression-cold")
runner.EVIDENCE = Path("/content/hrpoly-c6d-ambient-compression-cold-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-ambient-compression-cold-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-ambient-compression-cold-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMillsCore.lean": "f0fffb45c77137529b7c6706933f4f34345f7c1bf0bf31139d9a3fbfe76c348f",
    "tmp/c6d-ambient-compression-cold-boundary.json": "daaf4bbc0668425ff6dd2484bf8373c8f7800dce6586e95c02b67f300fc31c6a",
    "YangMills/RG/BalabanCMP99RegionalDirichletGaugePrecisionCompression.lean": "2eda2926400ecabd61a39203cae43cf9e0cc0d4c933cf3f7b2e21db11967c884",
    "YangMills/RG/BalabanCMP99RegionalDirichletGaugePrecisionCompressionAudit.lean": "82ad162d10dda12f4c1044d13cc9ff212a5e218bdc4a8ac73b4a05319f005bc2",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanion.lean": "8cc4786e1bcd99f59f5bb67d6924621b5b8816168f40e68cdbbd7262a5d643bf",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionAudit.lean": "c31f438ccca5eb0f800af4727d4348928a65585918ed822f69443156e47ad48a",
    "YangMills/RG/BalabanCMP99SourceGeneratedMassCompression.lean": "c081494faf04d96de77b2fe199877e3fbab26025e12cb5f557a841d5da11feff",
    "YangMills/RG/BalabanCMP99SourceGeneratedMassCompressionAudit.lean": "7233983345ebd12cd7440048c046146d35e6f68422f7562d72b0aa5c826d6f26",
    "YangMills/RG/BalabanCMP99SourceGeneratedPhysicalPrecisionCompression.lean": "5ecce0516fbbf7c5074648191ef3ce9e10a7096917d402d7633392c14e0bf79c",
    "YangMills/RG/BalabanCMP99SourceGeneratedPhysicalPrecisionCompressionAudit.lean": "9d5258383fd5acb9f3fee46098439f877248ca5b2721ab35ea69a216f263c512",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionPrecision.lean": "526b298651bb38696f7f9e413a55d5e1169dfec025bc656c87169a82f14a2572",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionPrecisionAudit.lean": "a1106bc63f99f1d5bf63a93667d9a7240e7c8996255ede6a8f5aa370ac61ece0",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecision.lean": "385c0ec9096922f417a5fa237782822c8f28b2419a671767b55769edbbddc4c3",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecisionAudit.lean": "fabb72011db4d2a814dd9cdf343b3a902e7781aaba4e8261c39befca9f378640",
    "YangMills/RG/BalabanCMP99ActiveGaugeRegionReindex.lean": "59ef01a9921edc96776819bfba63608500b53d740b5424137942d8b4131f75a3",
    "YangMills/RG/BalabanCMP99ActiveGaugeRegionReindexAudit.lean": "4a2c38554a745fa81e7efac2d02638fea536836d1785e43e055a42105d375989",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceAmbientBaselinePrecision.lean": "bfeda9d9bc9757feb4811442d905d0e0c0bdcb4425abff742e34dcd78bf206f0",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceAmbientBaselinePrecisionAudit.lean": "94987e48e14ef5bf1175a3f70b097fb46ec452967e0d9bebfe20541cfeec23d1",
    "YangMills/RG/BalabanCMP99ActiveGaugeRegionReindexGreen.lean": "0aa491a048fd5c6f5124b48d0b14915e8186868dbd0acb563e71ad0860fe8778",
    "YangMills/RG/BalabanCMP99ActiveGaugeRegionReindexGreenAudit.lean": "c0599cde262c0d69975db873f6e7a989cc8ac60125662df12c382a3cff6984c7",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionZeroDepth.lean": "f0bc6c5442e3a6d167e3159e069ad2215a30dd4554e5966eecdcb46f3faa6091",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionZeroDepthAudit.lean": "81a125caa8a6e0afa7269f4fa25b8c164f1e71cc99c31b5ac4b2b08e609499ca",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionZeroDepthGreen.lean": "c3f426fbcfdedc0caebafaf4e1b30fa803b1560ecf8586120a1e24a6814bad1d",
    "YangMills/RG/BalabanCMP99SourceActiveRegionFullCompanionZeroDepthGreenAudit.lean": "52a15153420814811ff68cdba5b6054bd1ec8e9bb1bb8dbe842df163871bc188",
}


def capturing_run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    stdout_path = runner.EVIDENCE / f"{stage}.stdout"
    with stdout_path.open("w", encoding="utf-8", newline="\n") as stream:
        child = subprocess.Popen(
            command, cwd=cwd, env=os.environ.copy(), text=True,
            stdout=stream, stderr=subprocess.STDOUT,
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
        + " SECONDS=%.3f" % elapsed, flush=True,
    )
    if returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = capturing_run

expected_manifest = {
    "classification": "PRE_VALIDATION_COLD_BOUNDARY",
    "seal_evidence_required": "fresh_checkout_no_lake_restore_plus_same_checkout_YangMillsCore",
    "terminal_counters_move": False,
    "pairs": [
        {
            "module": module,
            "source": f"YangMills/RG/{module}.lean",
            "audit": f"YangMills/RG/{module}Audit.lean",
            "expected_axiom_headers": expected,
        }
        for module, expected in MODULES
    ],
    "expected_pairs": 11,
    "expected_axiom_headers": 58,
}
manifest_gate = (
    "import json,pathlib;"
    "actual=json.loads(pathlib.Path('tmp/c6d-ambient-compression-cold-boundary.json').read_text());"
    f"expected=json.loads({json.dumps(json.dumps(expected_manifest))});"
    "assert actual==expected,(actual,expected);"
    "print('C6D_AMBIENT_COMPRESSION_MANIFEST_OK pairs=11 axioms=58')"
)

queue = [
    (
        "c6d_ambient_compression_manifest_gate",
        ["python3", "-c", manifest_gate],
        None,
    ),
    (
        "c6d_ambient_compression_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]

for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"c6d_ambient_compression_{index:02d}_{module.lower()}_source",
            ["lake", "build", f"YangMills.RG.{module}"],
            None,
        ),
        (
            f"c6d_ambient_compression_{index:02d}_{module.lower()}_audit",
            ["lake", "env", "lean", audit, "-o",
             f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean"],
            expected_axioms,
        ),
    ])

queue.append((
    "c6d_ambient_compression_root",
    ["lake", "build", "YangMillsCore"],
    None,
))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
