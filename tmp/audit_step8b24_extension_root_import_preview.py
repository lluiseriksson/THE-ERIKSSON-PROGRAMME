#!/usr/bin/env python3
"""Read-only staged root-import preview for the 17 Step 8b.24 extensions."""

from __future__ import annotations

import hashlib
from pathlib import Path
import re
import runpy
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tmp"))
S23 = runpy.run_path(str(ROOT / "tmp" / "audit_step8b23_brick_schedule.py"))["SCHEDULE"]
S24 = runpy.run_path(str(ROOT / "tmp" / "audit_step8b24_brick_schedule.py"))[
    "STEP8B24_SCHEDULE"
]
LATE = runpy.run_path(str(ROOT / "tmp" / "audit_step8b23_promotion_preview.py"))[
    "late_import_lines"
]
CORE = ROOT / "YangMillsCore.lean"
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)\s*$")


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest().upper()


def append_imports(content: str, additions: list[str]) -> tuple[str, str]:
    result = content.rstrip("\n") + "\n"
    rows: list[str] = []
    for index, addition in enumerate(additions, start=1):
        result += f"import {addition}\n"
        late = LATE(result)
        if late:
            raise ValueError(f"late root import after {addition}: {late}")
        rows.append(f"{index:02d}\t{addition}\t{sha(result)}\n")
    return result, sha("".join(rows))


def main() -> int:
    failures: list[str] = []
    prerequisite_names = [name for _, names in S23 for name in names]
    extension_names = [name for _, name in S24]
    prerequisites = [f"YangMills.RG.{name}Audit" for name in prerequisite_names]
    extensions = [f"YangMills.RG.{name}Audit" for name in extension_names]
    if len(prerequisites) != 22 or len(set(prerequisites)) != 22:
        failures.append("prerequisite audit-import scope is not 22 unique")
    if len(extensions) != 17 or len(set(extensions)) != 17:
        failures.append("extension audit-import scope is not 17 unique")

    original = CORE.read_text(encoding="utf-8-sig").replace("\r\n", "\n")
    existing = IMPORT.findall(original)
    if len(existing) != len(set(existing)):
        failures.append("YangMillsCore currently contains duplicate imports")
    present_prerequisites = [item for item in prerequisites if item in existing]
    present_extensions = [item for item in extensions if item in existing]
    if len(present_prerequisites) not in (0, 22):
        failures.append(
            f"partial Step8b23 root state: {len(present_prerequisites)}/22"
        )
    if present_extensions:
        failures.append(
            f"Step8b24 extension imports already present: {present_extensions}"
        )

    state = "ready" if len(present_prerequisites) == 22 else "future"
    prerequisite_base = original
    if state == "future":
        try:
            prerequisite_base, _ = append_imports(original, prerequisites)
        except ValueError as error:
            failures.append(str(error))
    else:
        positions = [existing.index(item) for item in prerequisites]
        if positions != sorted(positions):
            failures.append("Step8b23 root imports are not in schedule order")

    try:
        final, chain = append_imports(prerequisite_base, extensions)
    except ValueError as error:
        failures.append(str(error))
        final, chain = prerequisite_base, ""

    if failures:
        print("STEP8B24_EXTENSION_ROOT_IMPORT_PREVIEW_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    print(
        "STEP8B24_EXTENSION_ROOT_IMPORT_PREVIEW_OK "
        f"state={state} current_imports={len(existing)} "
        f"prerequisites_present={len(present_prerequisites)} "
        f"prerequisites_simulated={22 - len(present_prerequisites)} "
        f"extension_additions=17 final_imports={len(IMPORT.findall(final))} "
        f"prerequisite_base_sha256={sha(prerequisite_base)} "
        f"final_sha256={sha(final)} prefix_chain_sha256={chain}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
