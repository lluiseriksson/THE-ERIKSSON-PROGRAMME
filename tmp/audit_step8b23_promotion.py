#!/usr/bin/env python3
"""Read-only exact-scope audit for the Step 8b.23 promotion drafts."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
PATH_LISTS = (
    TMP / "STEP8B23-UNIT-E-PREFIX-PATHS.txt",
    TMP / "STEP8B23-UNIT-F-EXTENSION-PATHS.txt",
)
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)
PRINT = re.compile(r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_.'’]+)")
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)")
COMMENT_IMPORT = re.compile(r"(?m)^--\s*import\s+([^\s]+)")


def listed(path: Path) -> list[Path]:
    result: list[Path] = []
    for raw in path.read_text(encoding="utf-8-sig").splitlines():
        line = raw.strip()
        if line and not line.startswith("#"):
            result.append(ROOT / line)
    return result


def main() -> int:
    paths = [path for manifest in PATH_LISTS for path in listed(manifest)]
    failures: list[str] = []
    if len(paths) != 44 or len(set(paths)) != 44:
        failures.append(f"exact path scope is {len(paths)} files/{len(set(paths))} unique; expected 44/44")

    sources = [path for path in paths if not path.name.endswith("Audit.draft.lean")]
    audits = [path for path in paths if path.name.endswith("Audit.draft.lean")]
    if len(sources) != 22 or len(audits) != 22:
        failures.append(f"pair count source={len(sources)} audit={len(audits)}; expected 22/22")

    source_modules = {
        "YangMills.RG." + path.name.removesuffix(".draft.lean"): index
        for index, path in enumerate(sources)
    }
    tracked_names: dict[str, list[str]] = {}
    for path in (ROOT / "YangMills").rglob("*.lean"):
        for name in DECL.findall(path.read_text(encoding="utf-8-sig")):
            tracked_names.setdefault(name, []).append(path.relative_to(ROOT).as_posix())

    total_declarations = 0
    total_prints = 0
    all_names: dict[str, str] = {}
    for index, source in enumerate(sources):
        audit = TMP / source.name.replace(".draft.lean", "Audit.draft.lean")
        if not source.is_file():
            failures.append(f"missing source: {source.relative_to(ROOT)}")
            continue
        if not audit.is_file() or audit not in audits:
            failures.append(f"missing scoped sibling audit: {audit.relative_to(ROOT)}")
            continue

        target = ROOT / "YangMills" / "RG" / source.name.replace(".draft.lean", ".lean")
        if target.exists():
            failures.append(f"tracked target already exists: {target.relative_to(ROOT)}")

        declarations = DECL.findall(source.read_text(encoding="utf-8-sig"))
        prints = PRINT.findall(audit.read_text(encoding="utf-8-sig"))
        total_declarations += len(declarations)
        total_prints += len(prints)
        missing = [name for name in declarations if name not in prints]
        extra = [name for name in prints if name not in declarations]
        if missing:
            failures.append(f"audit missing {source.name}: {', '.join(missing)}")
        if extra:
            failures.append(f"audit extra {source.name}: {', '.join(extra)}")
        for name in declarations:
            prior = all_names.get(name)
            if prior is not None:
                failures.append(f"duplicate draft declaration: {name} ({prior}, {source.name})")
            all_names[name] = source.name
            for collision in tracked_names.get(name, []):
                failures.append(f"tracked declaration collision: {name} in {collision}")

        expected_audit_import = "YangMills.RG." + source.name.removesuffix(".draft.lean")
        audit_text = audit.read_text(encoding="utf-8-sig")
        audit_imports = IMPORT.findall(audit_text)
        commented_audit_imports = COMMENT_IMPORT.findall(audit_text)
        if audit_imports not in ([], [expected_audit_import]) or (
            expected_audit_import not in audit_imports + commented_audit_imports
        ):
            failures.append(
                f"audit import mismatch {audit.name}: expected [{expected_audit_import}] "
                f"active={audit_imports} commented={commented_audit_imports}"
            )

        for imported in IMPORT.findall(source.read_text(encoding="utf-8-sig")):
            if imported.startswith("Mathlib"):
                continue
            if not imported.startswith("YangMills.RG."):
                failures.append(f"unexpected import namespace {source.name}: {imported}")
                continue
            prior_index = source_modules.get(imported)
            if prior_index is not None:
                if prior_index >= index:
                    failures.append(f"forward draft import {source.name}: {imported}")
                continue
            tracked = ROOT / (imported.replace(".", "/") + ".lean")
            if not tracked.is_file():
                failures.append(f"unresolved tracked import {source.name}: {imported}")

    if failures:
        print("STEP8B23_PROMOTION_STATIC_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    print(
        "STEP8B23_PROMOTION_STATIC_OK "
        f"files={len(paths)} sources={len(sources)} audits={len(audits)} "
        f"declarations={total_declarations} prints={total_prints}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
