#!/usr/bin/env python3
"""Fail-closed static scope gate for Step-8b.24/C6c.2 P0--P1."""
from __future__ import annotations

import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PATH_LIST = ROOT / "tmp" / "STEP8B24-C6C2-P0-P1-PATHS.txt"
EXPECTED = {
    "tmp/P0CanonicalPrefixTower.lean":
        "21028CCBBB4DD660D8F9CBDCC144B37F5CF58E425AA5CD97DD8824A2671BEEFD",
    "tmp/P0CanonicalPrefixTowerAudit.lean":
        "E0CA421071FB337436D8B247C9DEF91708A0198D54A081A1A23341E4A9466307",
    "tmp/P1CoefficientMonotonicity.lean":
        "BF0724FAF5967A7A2A909A0919597FA21C81A96123832E1430E1A908A20A0382",
    "tmp/P1CoefficientMonotonicityAudit.lean":
        "890EFBDCAE9CB45C05CA8CBBBC35B3DD5FBBE1EE5A6F27458FF620C1BCED5A19",
}
EXPECTED_PATH_LIST_SHA256 = (
    "9663174609EA023FCC366661E68AB3E50E3A3934D64E0F3E804249AD97106001"
)
PAIRS = (
    ("tmp/P0CanonicalPrefixTower.lean", "tmp/P0CanonicalPrefixTowerAudit.lean", 10),
    ("tmp/P1CoefficientMonotonicity.lean", "tmp/P1CoefficientMonotonicityAudit.lean", 8),
)
EXPECTED_IMPORTS = {
    "tmp/P0CanonicalPrefixTower.lean":
        ("YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge",),
    "tmp/P0CanonicalPrefixTowerAudit.lean": ("tmp.P0CanonicalPrefixTower",),
    "tmp/P1CoefficientMonotonicity.lean": ("tmp.P0CanonicalPrefixTower",),
    "tmp/P1CoefficientMonotonicityAudit.lean": ("tmp.P1CoefficientMonotonicity",),
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def declarations(text: str) -> list[str]:
    return re.findall(
        r"(?m)^(?:noncomputable\s+)?(?:def|theorem|lemma|structure|class|abbrev)\s+"
        r"([A-Za-z0-9_'.]+)",
        text,
    )


def readouts(text: str) -> list[str]:
    prefix = "YangMills.RG."
    names = re.findall(r"(?m)^#print axioms\s+([A-Za-z0-9_'.]+)\s*$", text)
    if any(not name.startswith(prefix) for name in names):
        raise SystemExit("P0_P1_AUDIT_NAMESPACE_DRIFT")
    return [name.removeprefix(prefix) for name in names]


def main() -> int:
    path_bytes = PATH_LIST.read_bytes()
    if digest(path_bytes) != EXPECTED_PATH_LIST_SHA256:
        raise SystemExit("P0_P1_PATH_LIST_HASH_DRIFT")
    paths = [line for line in PATH_LIST.read_text(encoding="utf-8").splitlines() if line]
    if paths != list(EXPECTED):
        raise SystemExit("P0_P1_PATH_SCOPE_DRIFT")

    texts: dict[str, str] = {}
    for path in paths:
        data = (ROOT / path).read_bytes()
        if digest(data) != EXPECTED[path]:
            raise SystemExit(f"P0_P1_BLOB_HASH_DRIFT={path}/{digest(data)}")
        text = data.decode("utf-8")
        imports = tuple(re.findall(r"(?m)^import\s+([^\s]+)\s*$", text))
        if imports != EXPECTED_IMPORTS[path]:
            raise SystemExit(f"P0_P1_IMPORT_DRIFT={path}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"P0_P1_PLACEHOLDER={path}")
        texts[path] = text

    total = 0
    for source, audit, expected_count in PAIRS:
        source_names = declarations(texts[source])
        audit_names = readouts(texts[audit])
        if len(source_names) != expected_count or audit_names != source_names:
            raise SystemExit(
                f"P0_P1_READOUT_DRIFT={source}/decls={len(source_names)}/"
                f"prints={len(audit_names)}"
            )
        total += expected_count

    print(
        "STEP8B24_C6C2_P0_P1_STATIC_OK "
        f"files={len(paths)} bricks={len(PAIRS)} declarations={total} "
        f"axiom_readouts={total} compiler_verified=false counters=20/41 term_source=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
