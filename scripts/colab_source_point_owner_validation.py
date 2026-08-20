#!/usr/bin/env python3
"""Instrumental Colab gate for the generated point-source owner bound.

The wrapper reuses the already measured deterministic package-materialization
runner and changes only the exact source checkpoint, blob gates and focal
queue.  The imported runner is itself fetched by immutable Git SHA and
verified before execution.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "f49c32c30a790d313681c53b49b8fb90bbb34664"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bbd83565af5be389c997889bbea36e162bf2c68c/"
    "scripts/colab_source_fine_to_coarse_owner_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "e7bf2973a3274e60456081cbef7daacd34944e2915992e9f782807138518069f"
)
PARENT_RUNNER_PATH = Path("/content/colab_source_fine_to_coarse_owner_validation.py")


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location("point_owner_parent", PARENT_RUNNER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "source-point-owner-v2-transitive-prefix"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-point-owner")
runner.EVIDENCE = Path("/content/hrpoly-source-point-owner-evidence")
runner.ARCHIVE = Path("/content/hrpoly-source-point-owner-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-source-point-owner-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction.lean":
        "d26bc3785a6b0ca8acb2ceecd9e37a0352c88ac6d31261d330d9b1fd5d42556b",
    "YangMills/RG/BalabanCMP99FlatComplexFibrePointSourceFourierReconstructionAudit.lean":
        "17368a6bb63f939c3808d9c4260fbc46df8cfe6a5fc254ef80f4625356715f4c",
    "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral.lean":
        "af307c90c22f734b6717d3c4ce6a17c4be479479103f34f75b7ec638edcd3d74",
    "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentralAudit.lean":
        "ec2ab90cc02e542312fff97d5876aa27625c5218a68d9f1d43c8b1560041fcaa",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreen.lean":
        "7c99d36cdd48764825623a1678d7aaf24822b8b1b416ba939f3b2e2a9945866e",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenAudit.lean":
        "8da75f4c6cc4968d71f802de4d4b89a93bda7daa319af828f3b38b558ba78bba",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexification.lean":
        "86080ea66776b4b81113a228183b781f35bd31f078e5c11a1cb18672bd0885ff",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexificationAudit.lean":
        "3c397b46c4657834d1ab1dbdb325d8af8e83aed6946ad707faf9c14c83506871",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrand.lean":
        "7f7ff2f44d9d57342bb0a3eb438288b41068edd6138f41242fdd9c9d70da5395",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrandAudit.lean":
        "6ccd12de8ceaaaefc0a07caa34ce99e5cf3d2c58e3fac1872ddb54b9dc679141",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpoint.lean":
        "972ce47eb786bb6dde9ec61e79800712a381c556b313aa580dce7135abdfb78f",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpointAudit.lean":
        "95f5715e6c93769ff2bd39c0a5d32669f6cc913a2e20c4e30a1878b106a97431",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentification.lean":
        "015c8b782f892608499cdbed33f8eb982a97343af0fa075b331b0addc43c3612",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentificationAudit.lean":
        "b693686d00d3bd8f6c55387f4a04f66b3e9dd841d0172c0be0e6b0a2bdcd6bf0",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpoint.lean":
        "3c712d65fb93573b76ec1ffae44da5018ac78ac1225ca896f46ca919781ea403",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpointAudit.lean":
        "1a60a6c6141306d82ed4b4e0b63fcb573d29a9682f4990ebeef7186d6353b0a2",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBound.lean":
        "70842c878e6223ebbedf88f230e76644b99d106ad6bbaea98f77e5e539ad13f2",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBoundAudit.lean":
        "4d618354addaa277296e1115a3e2323598cf2915703a07341993f6fd207d0bd5",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceZeroResidue.lean":
        "206458b99c6529f6ff8767c753632ff9ff2774c53963c17ce2037f083cf2b071",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceZeroResidueAudit.lean":
        "fca5500445d4cae02976d43629d2d124a797edf98a9d69723226c359a806069d",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier.lean":
        "db89248f9269b0145472baa6d10a8cb7ed6250d6039ea1af49bc80c07cdae2c6",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrierAudit.lean":
        "39120f84a4455caada59b48936963432254b3960651d0d3b594a9a05a6f00904",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionary.lean":
        "0ff57eb90a2c2452da73af8e3eedc7aa4d70305087ba0d2c4b8961b057f318fe",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionaryAudit.lean":
        "20ca1999fa2d75422cb2e002ff7f3b3e982391af26ec88d9f23c8f49465a293e",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalZeroResidueAliasing.lean":
        "95d9eba09c4904c96ebf7d26124955a0a8ca0c4b10a178c5ae45562e53e92829",
    "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalZeroResidueAliasingAudit.lean":
        "b6acf48b604ce2f507dc0ff4d52b42a52a620824ae6c325f36ba381f2e269120",
}
runner.QUEUE = [
    (
        "point_owner_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBound",
        ],
        None,
    ),
    ("point_source_fourier_reconstruction_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99FlatComplexFibrePointSourceFourierReconstructionAudit.lean"], 4),
    ("mass_zero_noncentral_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentralAudit.lean"], 1),
    ("ambient_green_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenAudit.lean"], 5),
    ("ambient_green_complexification_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexificationAudit.lean"], 4),
    ("endpoint_integrand_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrandAudit.lean"], 1),
    ("green_fourier_endpoint_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpointAudit.lean"], 4),
    ("green_identification_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentificationAudit.lean"], 4),
    ("point_source_endpoint_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpointAudit.lean"], 1),
    ("point_source_zero_residue_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceZeroResidueAudit.lean"], 1),
    ("step7b_carrier_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrierAudit.lean"], 6),
    ("step7b_precision_dictionary_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionaryAudit.lean"], 2),
    ("zero_residue_aliasing_audit",
     ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalZeroResidueAliasingAudit.lean"], 4),
    (
        "point_owner_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceOwnerBoundAudit.lean",
        ],
        2,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
