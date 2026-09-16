#!/usr/bin/env python3
"""Fail-closed static scope gate for Step-8b.24/C6c.2 P0--P2c."""
from __future__ import annotations

import re

import audit_step8b24_c6c2_p0_p1_static as prefix

ROOT = prefix.ROOT
PATH_LIST = ROOT / "tmp" / "STEP8B24-C6C2-P0-P2-PATHS.txt"
EXPECTED_PATH_LIST_SHA256 = (
    "E1B145A10E9174FAF6915FF920551CA7633CCA38F875D96A9AE7294F49BEE15F"
)
P2_EXPECTED = {
    "tmp/P2SourceCoefficientCoercivity.lean":
        "47A6DA2EE8BC704A3ECFBFA28017AEC0E2137328956417F18E4857180F00F4C0",
    "tmp/P2SourceCoefficientCoercivityAudit.lean":
        "40712EE265161A31EECEB8002BF5DA48C882A7BBBCA4C0329F6729F8BA57DE75",
    "tmp/P2bEffectiveQuadratic.lean":
        "C4CD860BA0B83EE09505DAC966F982DC0ED4A7F216EEEB339B5D00E5C98EB71D",
    "tmp/P2bEffectiveQuadraticAudit.lean":
        "E344D5504C1A257E7DC1668C221B368F226540C253A8011314F8CA7CDF8E6792",
    "tmp/P2cCoarseCovariance.lean":
        "9C552B1F3F21B1253DAF8DDE15B36BBE09DDFBA18536D6EC4C166B3EBE4CC5E6",
    "tmp/P2cCoarseCovarianceAudit.lean":
        "D21C3756D1CCF15AE5B69CD4945BEBB542FEE853C6D9C5C0E2AC1DA12304B910",
}
P2_PAIRS = (
    ("tmp/P2SourceCoefficientCoercivity.lean",
     "tmp/P2SourceCoefficientCoercivityAudit.lean", 26),
    ("tmp/P2bEffectiveQuadratic.lean", "tmp/P2bEffectiveQuadraticAudit.lean", 10),
    ("tmp/P2cCoarseCovariance.lean", "tmp/P2cCoarseCovarianceAudit.lean", 24),
)
P2_IMPORTS = {
    "tmp/P2SourceCoefficientCoercivity.lean": (
        "tmp.P1CoefficientMonotonicity",
        "YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance",
    ),
    "tmp/P2SourceCoefficientCoercivityAudit.lean":
        ("tmp.P2SourceCoefficientCoercivity",),
    "tmp/P2bEffectiveQuadratic.lean": ("tmp.P2SourceCoefficientCoercivity",),
    "tmp/P2bEffectiveQuadraticAudit.lean": ("tmp.P2bEffectiveQuadratic",),
    "tmp/P2cCoarseCovariance.lean": ("tmp.P2bEffectiveQuadratic",),
    "tmp/P2cCoarseCovarianceAudit.lean": ("tmp.P2cCoarseCovariance",),
}


def main() -> int:
    prefix.main()
    if prefix.digest(PATH_LIST.read_bytes()) != EXPECTED_PATH_LIST_SHA256:
        raise SystemExit("P0_P2_PATH_LIST_HASH_DRIFT")
    paths = [line for line in PATH_LIST.read_text(encoding="utf-8").splitlines() if line]
    expected_paths = [*prefix.EXPECTED, *P2_EXPECTED]
    if paths != expected_paths:
        raise SystemExit("P0_P2_PATH_SCOPE_DRIFT")

    texts: dict[str, str] = {}
    for path, expected_hash in P2_EXPECTED.items():
        data = (ROOT / path).read_bytes()
        if prefix.digest(data) != expected_hash:
            raise SystemExit(f"P2_BLOB_HASH_DRIFT={path}/{prefix.digest(data)}")
        text = data.decode("utf-8")
        imports = tuple(re.findall(r"(?m)^import\s+([^\s]+)\s*$", text))
        if imports != P2_IMPORTS[path]:
            raise SystemExit(f"P2_IMPORT_DRIFT={path}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"P2_PLACEHOLDER={path}")
        texts[path] = text

    p2_total = 0
    for source, audit, expected_count in P2_PAIRS:
        source_names = prefix.declarations(texts[source])
        audit_names = prefix.readouts(texts[audit])
        if len(source_names) != expected_count or audit_names != source_names:
            raise SystemExit(
                f"P2_READOUT_DRIFT={source}/decls={len(source_names)}/"
                f"prints={len(audit_names)}"
            )
        p2_total += expected_count

    total = 18 + p2_total
    print(
        "STEP8B24_C6C2_P0_P2_STATIC_OK "
        f"files={len(paths)} bricks={2 + len(P2_PAIRS)} declarations={total} "
        f"axiom_readouts={total} compiler_verified=false counters=20/41 term_source=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
