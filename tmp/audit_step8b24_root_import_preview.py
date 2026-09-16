#!/usr/bin/env python3
"""Read-only preview of the 39 YangMillsCore audit-import additions."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

from audit_step8b23_brick_schedule import SCHEDULE as STEP8B23_SCHEDULE
from audit_step8b24_brick_schedule import STEP8B24_SCHEDULE
from audit_step8b23_promotion_preview import late_import_lines


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "YangMillsCore.lean"
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)\s*$")


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest().upper()


def main() -> int:
    first = [name for _, names in STEP8B23_SCHEDULE for name in names]
    names = first + [name for _, name in STEP8B24_SCHEDULE]
    failures: list[str] = []
    if len(names) != 39 or len(set(names)) != 39:
        failures.append(f"schedule={len(names)}/{len(set(names))}; expected 39/39")

    original = CORE.read_text(encoding="utf-8-sig").replace("\r\n", "\n")
    existing = IMPORT.findall(original)
    if len(existing) != len(set(existing)):
        failures.append("YangMillsCore currently contains duplicate imports")
    additions = [f"YangMills.RG.{name}Audit" for name in names]
    collisions = sorted(set(existing).intersection(additions))
    if collisions:
        failures.append(f"planned audit imports already present: {collisions}")
    if late_import_lines(original):
        failures.append("YangMillsCore already contains a late import")

    content = original.rstrip("\n") + "\n"
    prefix_manifest: list[str] = []
    for index, (name, addition) in enumerate(zip(names, additions, strict=True), start=1):
        content += f"import {addition}\n"
        late = late_import_lines(content)
        if late:
            failures.append(f"late root import after brick {index} {name}: {late}")
            break
        prefix_manifest.append(f"{index:02d}\t{name}\t{sha(content)}\n")

    final_imports = IMPORT.findall(content)
    if len(final_imports) != len(existing) + 39:
        failures.append(
            f"final import count delta {len(final_imports) - len(existing)}, expected 39"
        )
    if len(final_imports) != len(set(final_imports)):
        failures.append("preview creates duplicate root imports")

    if failures:
        print("STEP8B24_ROOT_IMPORT_PREVIEW_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    chain_sha256 = sha("".join(prefix_manifest))
    print(
        "STEP8B24_ROOT_IMPORT_PREVIEW_OK "
        f"base_imports={len(existing)} additions=39 final_imports={len(final_imports)} "
        f"base_sha256={sha(original)} final_sha256={sha(content)} "
        f"prefix_chain_sha256={chain_sha256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
