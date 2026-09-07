#!/usr/bin/env python3
"""Cold Colab validation for the source-fixed C6d coercivity/Green chain.

The queue checks the positive-radius Poincare prerequisite and nine promoted
source/audit pairs in dependency order, then builds YangMillsCore from the
same fresh checkout.  Eighty public declarations are audited.  This brick
constructs the literal baseline Green but does not attain window 15, move
20/41, or instantiate TermSource.
"""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.request


SOURCE_SHA = "2bb3eb7325b621954a7132d0a8bab3ce2c1bdf24"
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
    raise RuntimeError("C6D_SOURCE_COERCIVITY_GREEN_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location(
    "c6d_source_coercivity_green_base", BASE_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_SOURCE_COERCIVITY_GREEN_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

MODULES = [
    ("BalabanCMP99SourcePoincarePositiveRadiusReachability", 9),
    ("BalabanCMP99SourceWeightedGaugePrecisionDictionary", 3),
    ("BalabanCMP99Eq360WeightedPrecisionRealSlice", 1),
    ("BalabanCMP99SourceActiveRegionTerminalCoercivity", 8),
    ("BalabanCMP99Eq360C6dLaplacianRetainedExtension", 6),
    ("BalabanCMP99Eq360C6dLocalizedRetainedPrecision", 30),
    ("BalabanCMP99Eq360C6dSourceFixedInput", 11),
    ("BalabanCMP99Eq360C6dSourceTerminalCoercivity", 3),
    ("BalabanCMP99Eq360C6dSourceTerminalCoercivityReachability", 1),
    ("BalabanCMP99Eq360C6dSourceBaselineGreen", 8),
]

runner.RUNNER_REV = "c6d-source-coercivity-green-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6d-source-coercivity-green")
runner.EVIDENCE = Path("/content/hrpoly-c6d-source-coercivity-green-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-source-coercivity-green-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-source-coercivity-green-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMillsCore.lean": "be0f6428743724d16de315ddc455e2df684823c6e3a4d1c28f283a409e283427",
    "YangMills/RG/BalabanCMP99SourcePoincarePositiveRadiusReachability.lean": "1c9d571f67b65b5f14a23580bfaf13d746b817dcb1b44554b9aeab3add5f9571",
    "YangMills/RG/BalabanCMP99SourcePoincarePositiveRadiusReachabilityAudit.lean": "e2ce07a504bdb44cc71b97d39294af043e00fa90cf56f10918736c722d198c20",
    "YangMills/RG/BalabanCMP99SourceWeightedGaugePrecisionDictionary.lean": "f0e0d45b2569b833b196e56c041f251714ccdef00fde95b694fb40c72f04ef96",
    "YangMills/RG/BalabanCMP99SourceWeightedGaugePrecisionDictionaryAudit.lean": "6f0f5f4adc6f5450d4e181138477f3978886d5fba5bf248db0c01ef4f24a05bf",
    "YangMills/RG/BalabanCMP99Eq360WeightedPrecisionRealSlice.lean": "b592af9124c8dee81491e4c143893da8b23b45e7d6a3f56cb4ad2aee8481d608",
    "YangMills/RG/BalabanCMP99Eq360WeightedPrecisionRealSliceAudit.lean": "1a97f32e9a35c7023e5f5fce948dad43fd55cd5c7ecc0fff663d8b5d5eaf88dd",
    "YangMills/RG/BalabanCMP99SourceActiveRegionTerminalCoercivity.lean": "d8bdca5556932938ca01b05512ff078c6f29c596f4b208582d782782caa0d8b9",
    "YangMills/RG/BalabanCMP99SourceActiveRegionTerminalCoercivityAudit.lean": "461c8036da5c9730670ea55b485cf7a88dfc41ffabaff2d2102814f2c10883bb",
    "YangMills/RG/BalabanCMP99Eq360C6dLaplacianRetainedExtension.lean": "20893cad8a6973d7bd0facaf1fad3fd57c13badf5a802840917a384cae7c381c",
    "YangMills/RG/BalabanCMP99Eq360C6dLaplacianRetainedExtensionAudit.lean": "fcc08ddf76e43ab1f7ad0f64f3bcb0b14ad35452ee1f29fc9993545128537145",
    "YangMills/RG/BalabanCMP99Eq360C6dLocalizedRetainedPrecision.lean": "d03a0f3f83f8166750c2c76cd13d1ae352f624532b0facba490ea68e71949de1",
    "YangMills/RG/BalabanCMP99Eq360C6dLocalizedRetainedPrecisionAudit.lean": "cb784bd626bd1740cf6be3251969fe25aa84b350fd1eddd46e578e10ee685b9f",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceFixedInput.lean": "27ed6c6e5a3ad2f7323631ae4122b1848effc12875168818df6e1953319eb4d1",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceFixedInputAudit.lean": "dc0a1d61ea117ce8eb3da39a3aa74bc9cfb49837ea5fbb97e1cf421ec3909437",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceTerminalCoercivity.lean": "09a3b4bcd25e493fc4590842e8cdd65f10062cd654f93f721f789eae6c5eb95e",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceTerminalCoercivityAudit.lean": "b1d480c616ba5fa60a3989ec334f38d12531d0900ef43f984d2699abee9f0172",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceTerminalCoercivityReachability.lean": "e360b6b87f10853678965bb299967c790d10d11d3891daaed68518c5741312c1",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceTerminalCoercivityReachabilityAudit.lean": "44b3fe4e7dfb0473c78b996b6e6f42b1eea69a845d68ea192c9462aeab980f55",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceBaselineGreen.lean": "4f9dcf11c47ff3d7f6b3af8a39c87f7cdfd94b4536b49750553dfeca815f2a61",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceBaselineGreenAudit.lean": "97d254f932c1361d7906394cf2568023dd4257ddfac24ed70729c361ddc3a87f",
}


def capturing_run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command, cwd=cwd, env=os.environ.copy(), text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    output = child.stdout
    print(output, flush=True)
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    (runner.EVIDENCE / f"{stage}.stdout").write_text(
        output, encoding="utf-8", newline="\n"
    )
    runner.RECORDS.append({
        "stage": stage,
        "exit": child.returncode,
        "seconds": elapsed,
        "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
    })
    print(
        "STAGE=" + stage + " EXIT=" + str(child.returncode)
        + " SECONDS=%.3f" % elapsed, flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = capturing_run

dependencies = [
    "YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreen",
    "YangMills.RG.BalabanCMP109PhysicalPivotSmallnessCompatibility",
    "YangMills.RG.BalabanCMP99Eq335PhysicalRetainedNearIdentity",
    "YangMills.RG.BalabanCMP99SourceGaugePrecision",
    "YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime",
    "YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance",
    "YangMills.RG.BalabanCMP99Eq360ComplexRegionalPrecisionPerturbation",
    "YangMills.RG.BalabanCMP99Eq359TowerRealSliceAgreement",
    "YangMills.RG.BalabanCMP85SourcePrefixGreen",
    "YangMills.RG.BalabanCMP99SourceMassWeights",
    "YangMills.RG.BalabanCMP99Eq335PhysicalLaplacianInternalCarrier",
    "YangMills.RG.BalabanCMP99SourceLocalizedRetainedTower",
    "YangMills.RG.BalabanCMP99SourcePhysicalRealSliceTowerPair",
    "YangMills.RG.BalabanCMP99Eq337ComplexClosedRadiusToPhysicalRadiusBudget",
    "YangMills.RG.BalabanCMP99SourceRetainedFineOneCochainExtension",
    "YangMills.RG.BalabanCMP99Eq360ComplexRegionalLaplacian",
    "YangMills.RG.BalabanCMP99Eq360ComplexRegionalLaplacianRealSlice",
    "YangMills.RG.BalabanCMP99Eq360ComplexLocalLaplacianPerturbation",
    "YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision",
    "YangMills.RG.BalabanCMP99Eq337PhysicalComplexBaselineRealSlice",
    "YangMills.RG.BalabanCMP99SourceUbarRadiusBudget",
    "YangMills.RG.BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridge",
]
queue = [
    (
        "c6d_source_coercivity_green_materialize_dependencies",
        ["lake", "build", *dependencies],
        None,
    ),
    (
        "c6d_source_coercivity_green_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
]

for index, (module, expected_axioms) in enumerate(MODULES, start=1):
    source = f"YangMills/RG/{module}.lean"
    audit = f"YangMills/RG/{module}Audit.lean"
    queue.extend([
        (
            f"c6d_source_coercivity_green_{index:02d}_{module.lower()}_source",
            ["lake", "env", "lean", source, "-o",
             f".lake/build/lib/lean/YangMills/RG/{module}.olean"],
            None,
        ),
        (
            f"c6d_source_coercivity_green_{index:02d}_{module.lower()}_audit",
            ["lake", "env", "lean", audit, "-o",
             f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean"],
            expected_axioms,
        ),
    ])

queue.append((
    "c6d_source_coercivity_green_root",
    ["lake", "build", "YangMillsCore"],
    None,
))
runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
