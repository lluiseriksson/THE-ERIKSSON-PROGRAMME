#!/usr/bin/env python3
"""Fresh Colab gate for the CMP89 uniform owner-kernel certificate."""

from __future__ import annotations

import traceback
from pathlib import Path

import colab_cmp89_neumann_rectangular_physical_uniform_owner_validation as gate


gate.RUNNER_REV = "cmp89-neumann-physical-uniform-owner-certificate-v1"
gate.SOURCE_SHA = "40f025a2cfc080b7ae2db85c780f68d931c37d25"
gate.ROOT = gate.CONTENT / "hrpoly-cmp89-uniform-owner-certificate-cold-40f025a2"
gate.EVIDENCE = gate.CONTENT / "hrpoly-cmp89-uniform-owner-certificate-cold-40f025a2-evidence"
gate.ARCHIVE = gate.CONTENT / "hrpoly-cmp89-uniform-owner-certificate-cold-40f025a2-evidence.tar.gz"
gate.PATH_MANIFEST = gate.CONTENT / "hrpoly-cmp89-uniform-owner-certificate-paths.txt"
gate.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalUniformOwnerCertificate.lean":
        "34f1ce3a3db1cca2c6ffe13f11bdeba1a71c2e847ad09f5945cb4e9096cbc617",
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalUniformOwnerCertificateAudit.lean":
        "d4f61fea91182bcdbbc34d034465400aa4c6d142e9a31c32c00f0ce579cc33f2",
    "YangMillsCore.lean":
        "f4808a830250c8f32b327a7db7d3132e696697446c9f6e411cc09c66401836e6",
}
gate.EXPECTED_DECLARATIONS = [
    "YangMills.RG.CMP89RegionalOwnerKernelDecayCertificate",
    "YangMills.RG.cmp89Eq248PhysicalRegionalUniformOwnerB0_draft",
    "YangMills.RG.cmp89Eq248PhysicalRegionalOwnerKernelDecayCertificate_draft",
]
gate.RECORDS.clear()


def main() -> int:
    opened = gate.utc_now()
    status = "FAIL"
    print("RUNNER_REV=" + gate.RUNNER_REV, flush=True)
    print("STAGE=runtime_open UTC=" + opened, flush=True)
    try:
        import psutil

        ram_gib = psutil.virtual_memory().total / 2**30
        print(f"RUNTIME=CPU RAM_GIB={ram_gib:.2f}", flush=True)
        if Path("/dev/nvidia0").exists():
            raise RuntimeError("GPU_RUNTIME_NOT_AUTHORIZED")
        if ram_gib < 40:
            raise RuntimeError("HIGH_RAM_REQUIRED")
        for path in (gate.ROOT, gate.EVIDENCE, gate.ARCHIVE):
            if path.exists():
                raise RuntimeError("FRESH_PATH_ALREADY_EXISTS=" + str(path))

        gate.ensure_toolchain()
        gate.run("clone", ["git", "clone", "--no-tags", gate.REPO_URL, str(gate.ROOT)])
        gate.run("checkout", ["git", "checkout", "--detach", gate.SOURCE_SHA], cwd=gate.ROOT)
        head = gate.run("head", ["git", "rev-parse", "HEAD"], cwd=gate.ROOT).strip()
        if head != gate.SOURCE_SHA:
            raise RuntimeError("HEAD_MISMATCH=" + head)
        for relative, expected in gate.SOURCE_BLOBS.items():
            actual = gate.sha256(gate.ROOT / relative)
            print(f"SOURCE_BLOB={relative} SHA256={actual}", flush=True)
            if actual != expected:
                raise RuntimeError("SOURCE_BLOB_HASH_MISMATCH=" + relative)

        source_paths = [path for path in gate.SOURCE_BLOBS if path != "YangMillsCore.lean"]
        gate.PATH_MANIFEST.write_text("\n".join(source_paths) + "\n", encoding="utf-8")
        gate.run(
            "overlay_text_guard",
            [
                "python3", "scripts/check_lean_overlay_text.py",
                "--paths-from", str(gate.PATH_MANIFEST), "--require-prevalidation",
            ],
            cwd=gate.ROOT,
        )
        gate.run(
            "import_prefix_guard",
            ["python3", "scripts/check_lean_import_prefix.py", *gate.SOURCE_BLOBS],
            cwd=gate.ROOT,
        )
        if (gate.ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() != gate.EXPECTED_TOOLCHAIN:
            raise RuntimeError("LEAN_TOOLCHAIN_FILE_MISMATCH")
        manifest_before = gate.sha256(gate.ROOT / "lake-manifest.json")
        toolchain_before = gate.sha256(gate.ROOT / "lean-toolchain")
        gate.run("lake_update", ["lake", "update"], cwd=gate.ROOT)
        if gate.sha256(gate.ROOT / "lake-manifest.json") != manifest_before:
            raise RuntimeError("MANIFEST_DRIFT")
        if gate.sha256(gate.ROOT / "lean-toolchain") != toolchain_before:
            raise RuntimeError("TOOLCHAIN_FILE_DRIFT")
        mathlib = gate.run(
            "mathlib_pin",
            ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
            cwd=gate.ROOT,
        ).strip()
        if mathlib != gate.EXPECTED_MATHLIB:
            raise RuntimeError("MATHLIB_PIN_MISMATCH=" + mathlib)
        gate.run("cache_get", ["lake", "exe", "cache", "get"], cwd=gate.ROOT)
        gate.run(
            "physical_uniform_owner_certificate_focal",
            [
                "lake", "build",
                "YangMills.RG.BalabanCMP89NeumannRectangularPhysicalUniformOwnerCertificate",
            ],
            cwd=gate.ROOT,
        )
        audit = gate.run(
            "physical_uniform_owner_certificate_audit",
            [
                "lake", "env", "lean",
                "YangMills/RG/"
                "BalabanCMP89NeumannRectangularPhysicalUniformOwnerCertificateAudit.lean",
            ],
            cwd=gate.ROOT,
        )
        gate.parse_axioms_exact(audit)
        status = "PASS"
    except Exception as error:
        print("ERROR=" + repr(error), flush=True)
        traceback.print_exc()
    finally:
        evidence_hash, manifest_hash, archive_hash = gate.make_evidence(status, opened)
        print("EVIDENCE_JSON_SHA256=" + evidence_hash, flush=True)
        print("EVIDENCE_MANIFEST_SHA256=" + manifest_hash, flush=True)
        print("EVIDENCE_ARCHIVE=" + str(gate.ARCHIVE), flush=True)
        print("EVIDENCE_ARCHIVE_SHA256=" + archive_hash, flush=True)
        print("FINAL_STATUS=" + status, flush=True)
        print("RUNTIME_RETAINED_FOR_EVIDENCE_DOWNLOAD=1", flush=True)
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
