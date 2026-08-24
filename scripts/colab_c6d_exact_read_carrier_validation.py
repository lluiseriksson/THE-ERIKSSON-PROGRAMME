#!/usr/bin/env python3
"""Cold gate for the promoted C6d exact-read-carrier prefix.

The runner clones immutable ``SOURCE_SHA``, verifies the 36 promoted modules,
the root aggregator and the path manifest, builds ``YangMillsCore``, and runs
all 18 direct axiom audits stop-on-first-error. It does not remove any
PRE-VALIDATION notice.
"""

import hashlib
import importlib.util
from pathlib import Path
import re
import urllib.request


SOURCE_SHA = "f214b795f804f0d05cc64fd851b45eaa2532523a"
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
    raise RuntimeError("C6D_READ_CARRIER_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("c6d_read_carrier_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_READ_CARRIER_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

ROOT_MODULE = "YangMillsCore.lean"
PATH_MANIFEST = "tmp/C6D-EXACT-READ-CARRIER-PROMOTED-PATHS.txt"

AUDITS = (
    ("ubar_exact", "YangMills/RG/BalabanCMP99SourceUbarExactReadCarrierAudit.lean", 9),
    ("average_exact", "YangMills/RG/BalabanCMP99SourceTransportedAverageExactReadCarrierAudit.lean", 4),
    ("retained_exact", "YangMills/RG/BalabanCMP99SourceRetainedExactReadCarrierAudit.lean", 7),
    ("endpoint_geometry", "YangMills/RG/BalabanCMP99SourceRetainedCarrierEndpointGeometryAudit.lean", 10),
    ("laplacian_locality", "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityLaplacianLocalityAudit.lean", 9),
    ("ubar_deviation", "YangMills/RG/BalabanCMP99SourceUbarLocalDeviationBoundAudit.lean", 3),
    ("next_locality", "YangMills/RG/BalabanCMP99SourceSelectedNextBackgroundLocalityAudit.lean", 4),
    ("localized_next", "YangMills/RG/BalabanCMP99SourceLocalizedNextBackgroundAudit.lean", 8),
    ("localized_qprime", "YangMills/RG/BalabanCMP99SourceLocalizedWeightedQprimeTowerAudit.lean", 3),
    ("retained_qprime", "YangMills/RG/BalabanCMP99SourceRetainedQprimeLocalityAudit.lean", 1),
    ("canonical_extension", "YangMills/RG/BalabanCMP99SourceLocalizedTowerCanonicalExtensionAudit.lean", 2),
    ("fine_extension", "YangMills/RG/BalabanCMP99SourceRetainedFineExtensionAudit.lean", 5),
    ("retained_tower", "YangMills/RG/BalabanCMP99SourceLocalizedRetainedTowerAudit.lean", 3),
    ("near_identity", "YangMills/RG/BalabanCMP99Eq335PhysicalRetainedNearIdentityAudit.lean", 5),
    ("source_dictionary", "YangMills/RG/BalabanCMP99Eq335SourceRegionDictionaryAudit.lean", 2),
    ("physical_tower", "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerAudit.lean", 2),
    ("source_region_tower", "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegionAudit.lean", 2),
    ("class_source_region", "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTowerAudit.lean", 2),
)

runner.RUNNER_REV = "c6d-exact-read-carrier-cold-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6d-exact-read-carrier")
runner.EVIDENCE = Path("/content/hrpoly-c6d-exact-read-carrier-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-exact-read-carrier-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-exact-read-carrier-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceUbarExactReadCarrier.lean": "adb3422777c101ca3e4683f36a687e78e6f9e09aed61c399370bda8cf6d36835",
    "YangMills/RG/BalabanCMP99SourceUbarExactReadCarrierAudit.lean": "5291b2a5388140f6895c58aa41be306b95c6978813be1da2b734ffbdc6bde06b",
    "YangMills/RG/BalabanCMP99SourceTransportedAverageExactReadCarrier.lean": "ff03b98523ad31a8b94a7f83a028828c31d8485e46a035a32b839d97159d6829",
    "YangMills/RG/BalabanCMP99SourceTransportedAverageExactReadCarrierAudit.lean": "7ed64dd89e6affeca0b3565aa4ccf5bcadde3b61559e6f9907952460341c4f3b",
    "YangMills/RG/BalabanCMP99SourceRetainedExactReadCarrier.lean": "a139eaa5477b20f7d56cedef46fb1566aa12cc3e02174c6e177913be637c1374",
    "YangMills/RG/BalabanCMP99SourceRetainedExactReadCarrierAudit.lean": "86b3f622e16b0da07dee435a4770b72c64172f1a29d833c05c5d1bb216219a28",
    "YangMills/RG/BalabanCMP99SourceRetainedCarrierEndpointGeometry.lean": "3641d88103557d1d43a40dbec3cf1962c0c2aab2128c41b3e312db4d6b1ff1af",
    "YangMills/RG/BalabanCMP99SourceRetainedCarrierEndpointGeometryAudit.lean": "5ac9dacf229e274b3ff870bf4a0077f45ca881c337a5c3c1a2eb9c25f5c02b08",
    "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityLaplacianLocality.lean": "c61e655058e81bf2e20c13f9426db690c49e7c80ea3c2a3886156d629c0e3bcf",
    "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityLaplacianLocalityAudit.lean": "f503b6920e9c7db5659916e22fbba408bde50979bc43c58cf432545da14620c9",
    "YangMills/RG/BalabanCMP99SourceUbarLocalDeviationBound.lean": "9baa638f41e2345848ab9cca80d2b5d50f2e9a29d86f9ffd0e1916fe21e0e4bc",
    "YangMills/RG/BalabanCMP99SourceUbarLocalDeviationBoundAudit.lean": "26c99419711f8616ae553b3ac1d56af5b21cc8fb3c57b5fc89859b6ae53805d3",
    "YangMills/RG/BalabanCMP99SourceSelectedNextBackgroundLocality.lean": "ab8a09be7e31a936b4d9aa89b0133fdd871ef3a2f70b34ee7ddeae396a09aa4b",
    "YangMills/RG/BalabanCMP99SourceSelectedNextBackgroundLocalityAudit.lean": "7f03daca9ab36370346ae292f430005226b2825e4dafa9a9acdc7d737b253dee",
    "YangMills/RG/BalabanCMP99SourceLocalizedNextBackground.lean": "8d1e39a3c351ed50043ffeeb96258433eb910886170594968ff9888dce3c9240",
    "YangMills/RG/BalabanCMP99SourceLocalizedNextBackgroundAudit.lean": "ce95b9e8156695d34dff9a4837d0fb743cc8649cd4601e44b29ad5cda96932cb",
    "YangMills/RG/BalabanCMP99SourceLocalizedWeightedQprimeTower.lean": "88d4b0f64a1fadc1832cbb06a6e1f1a44ba4fd8c30a810d212467ffaec579a1c",
    "YangMills/RG/BalabanCMP99SourceLocalizedWeightedQprimeTowerAudit.lean": "23a128e59ac5576b8a742da222c51b8f345b1debd73976004ea6026954da20e8",
    "YangMills/RG/BalabanCMP99SourceRetainedQprimeLocality.lean": "2323ed1c7eacb00b604b9844e92528ceefe7247fdab53a59defabc29ff8fbd7e",
    "YangMills/RG/BalabanCMP99SourceRetainedQprimeLocalityAudit.lean": "719594623c1a3363c082318e5865b90a68de77f1b30809b1ca38dcd5c6a78cf8",
    "YangMills/RG/BalabanCMP99SourceLocalizedTowerCanonicalExtension.lean": "d342cf65c8e0a6db0ad5691eed3110493c369631abca3f57545f106d3e4dcba1",
    "YangMills/RG/BalabanCMP99SourceLocalizedTowerCanonicalExtensionAudit.lean": "7555d88de4640be8a45088f8c9e6cfdb782ab03fad21e789b7172252a3df2709",
    "YangMills/RG/BalabanCMP99SourceRetainedFineExtension.lean": "4f11a4e2b29a5bb3d835e717a224bfaba44cfe009fb2882e216314f990928f5b",
    "YangMills/RG/BalabanCMP99SourceRetainedFineExtensionAudit.lean": "f04cb5a0c105dca9a515fb92ece09da3b5cc41b5a5743badbb7e085516bdd403",
    "YangMills/RG/BalabanCMP99SourceLocalizedRetainedTower.lean": "2818165fe0f2779515ec524aeb1acf947c16e361999bac4c80e21bbfe2ebb624",
    "YangMills/RG/BalabanCMP99SourceLocalizedRetainedTowerAudit.lean": "5c410626909a2aaccb7ae484bb7e3d84fa23c9b70a6822286d307c4ec61f4de5",
    "YangMills/RG/BalabanCMP99Eq335PhysicalRetainedNearIdentity.lean": "5af8dddc2bf3b519429f2f3e8a9f48cbc6677f5991309f78fe72ebedd812153b",
    "YangMills/RG/BalabanCMP99Eq335PhysicalRetainedNearIdentityAudit.lean": "00f07601eda2355e9f909069ba6d0e091483ca41c50a634e7e2c9907bc7c2176",
    "YangMills/RG/BalabanCMP99Eq335SourceRegionDictionary.lean": "74de39d22423ffe4169abc16085aae3f678b4e67f2e6436f928bb6ad5af08a64",
    "YangMills/RG/BalabanCMP99Eq335SourceRegionDictionaryAudit.lean": "0ea35d15dc77eb92d3a01d6a2ec8d196df2038578cb1b00013b0141343b5702e",
    "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTower.lean": "ac716006f693636831507d45f9192c019a3a3fd09f10094d186011f253a8b103",
    "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerAudit.lean": "55d372987cd7e4f21143f53d78cb6851d83495a31fd64817d971a4defc0a521c",
    "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion.lean": "766a608169d73e3a95fb433a672aa4b480f5794bf896310283bc9d22d3f9d589",
    "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegionAudit.lean": "3a43f4db35a374160b9aadf37913cf29b1e9547dc1b9a94fa10d25dcaf40bd0d",
    "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTower.lean": "4bfb3d2748581860a7178795ef3cfe01566d895d7f4c21c667e91303613fd7a0",
    "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTowerAudit.lean": "aefd4126cf1182f13f2c5d10ade4d903ad71e63e59c7aabe9924704c491f4896",
    ROOT_MODULE: "dabba854357f0abf6b2d994e5a96efc8271358d6c45c66dea9a087cfa4bb2479",
    PATH_MANIFEST: "19313f826ce0d4b83d8acea9b9bab31451ef8da8fc72773573b9b39478b06fcf",
}


def parse_axioms_including_pure(output: str, expected: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = re.findall(r"doesnotdependonanyaxioms", compact)
    if len(blocks) + len(pure) != expected:
        raise RuntimeError(
            f"AXIOM_READOUT_COUNT={len(blocks)}+{len(pure)} EXPECTED={expected}"
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET_{index}={sorted(names)}")


runner.parse_axioms = parse_axioms_including_pure
runner.QUEUE = [
    ("c6d_read_carrier_root", ["lake", "build", "YangMillsCore"], None),
] + [
    ("c6d_read_carrier_" + stage, ["lake", "env", "lean", path], expected)
    for stage, path, expected in AUDITS
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
