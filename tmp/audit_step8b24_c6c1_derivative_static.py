#!/usr/bin/env python3
"""Fail-closed static audit of the unelaborated C6c.1 D1--D4d queue.

This script performs no Lean/Lake work and writes nothing.  It fixes the
ordered source/audit pairs, checks exact declaration/readout ownership and
dependency direction, verifies that no tracked promotion target already
exists, and computes both raw-draft and deterministic PRE-VALIDATION content
manifests.  A green result is instrumentation evidence only.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import re
import runpy
import sys


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
sys.path.insert(0, str(TMP))
PROMOTION = runpy.run_path(str(TMP / "audit_step8b24_promotion_preview.py"))

SCHEDULE: tuple[tuple[str, str], ...] = (
    ("D1", "BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformHolomorphy"),
    ("D2a", "BalabanCMP89Eq249FineLatticeLeftDerivativeOneCoordinateContourShift"),
    ("D2b", "BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope"),
    ("D3", "BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformBound"),
    ("D4a-b", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativeResidueShift"),
    ("D4c", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalDerivativePeriodization"),
    ("D4d", "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceDerivative"),
)
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)
PRINT = re.compile(r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_.'’]+)")
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)")
COMMENT_IMPORT = re.compile(r"(?m)^--\s*import\s+([^\s]+)")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def main() -> int:
    failures: list[str] = []
    names = [name for _, name in SCHEDULE]
    positions = {name: index for index, name in enumerate(names)}
    raw_rows: list[str] = []
    promoted_rows: list[str] = []
    declaration_total = 0
    dependency_total = 0

    path_manifest = TMP / "STEP8B24-C6C1-D4-PATHS.txt"
    d4_paths = {
        (ROOT / line.strip()).resolve()
        for line in path_manifest.read_text(encoding="utf-8-sig").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    }
    expected_d4 = {
        (TMP / f"{name}{suffix}").resolve()
        for _, name in SCHEDULE[4:]
        for suffix in (".draft.lean", "Audit.draft.lean")
    }
    if d4_paths != expected_d4:
        failures.append(
            "D4 path scope mismatch "
            f"missing={sorted(str(p.name) for p in expected_d4 - d4_paths)} "
            f"extra={sorted(str(p.name) for p in d4_paths - expected_d4)}"
        )

    for index, (brick, name) in enumerate(SCHEDULE):
        source = TMP / f"{name}.draft.lean"
        audit = TMP / f"{name}Audit.draft.lean"
        target = ROOT / "YangMills" / "RG" / f"{name}.lean"
        target_audit = ROOT / "YangMills" / "RG" / f"{name}Audit.lean"
        if not source.is_file() or not audit.is_file():
            failures.append(f"missing pair: {brick}/{name}")
            continue
        if target.exists() or target_audit.exists():
            failures.append(f"tracked promotion target already exists: {name}")

        source_text = source.read_text(encoding="utf-8-sig")
        audit_text = audit.read_text(encoding="utf-8-sig")
        declarations = DECL.findall(source_text)
        prints = PRINT.findall(audit_text)
        if declarations != prints:
            failures.append(
                f"ordered declaration/audit mismatch: {brick}/{name} "
                f"decl={declarations} print={prints}"
            )
        declaration_total += len(declarations)

        imports = IMPORT.findall(source_text) + COMMENT_IMPORT.findall(source_text)
        internal = []
        for imported in imports:
            dependency = imported.removeprefix("YangMills.RG.")
            if dependency in positions:
                internal.append(dependency)
                if positions[dependency] >= index:
                    failures.append(f"forward dependency: {name} -> {dependency}")
        dependency_total += len(set(internal))

        for draft, promoted_target in ((source, target), (audit, target_audit)):
            raw = draft.read_bytes()
            raw_rows.append(
                f"{hashlib.sha256(raw).hexdigest()}  "
                f"{draft.relative_to(ROOT).as_posix()}\n"
            )
            try:
                promoted = PROMOTION["transform"](draft)[0]
                promoted_rows.append(
                    f"{hashlib.sha256(promoted).hexdigest()}  "
                    f"{promoted_target.relative_to(ROOT).as_posix()}\n"
                )
            except (OSError, RuntimeError, ValueError) as error:
                failures.append(f"promotion transform {draft.name}: {error}")

    if len(raw_rows) != 14 or len(promoted_rows) != 14:
        failures.append(
            f"manifest scope raw={len(raw_rows)} promoted={len(promoted_rows)} expected=14"
        )
    if failures:
        print("STEP8B24_C6C1_DERIVATIVE_STATIC_AUDIT_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    print(
        "STEP8B24_C6C1_DERIVATIVE_STATIC_AUDIT_OK "
        f"bricks={len(SCHEDULE)} files={len(raw_rows)} "
        f"declarations={declaration_total} dependencies={dependency_total} "
        f"raw_manifest_sha256={sha(''.join(raw_rows).encode())} "
        f"promotion_manifest_sha256={sha(''.join(promoted_rows).encode())} "
        "compiler_verified=false counters=20/41 term_source=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
