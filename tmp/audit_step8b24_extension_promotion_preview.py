#!/usr/bin/env python3
"""Staged Step 8b.24 preview after the 22 Step 8b.23 bricks are sealed.

The older 78-file aggregate preview remains useful as a whole-graph static
audit, but cannot be the promotion mechanism after staged A--F sealing.  This
preview treats the 44 sealed A--F targets as immutable prerequisites, creates
only the 34 S1--C6b targets, and includes the one neutral-theorem ownership
move in the same content manifest.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import runpy
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tmp"))
P23 = runpy.run_path(str(ROOT / "tmp" / "audit_step8b23_promotion_preview.py"))
P24 = runpy.run_path(str(ROOT / "tmp" / "audit_step8b24_promotion_preview.py"))
SCHEDULE = runpy.run_path(str(ROOT / "tmp" / "audit_step8b24_brick_schedule.py"))
OWNERSHIP = runpy.run_path(str(ROOT / "tmp" / "audit_step8b24_ownership_move.py"))


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def target(name: str, *, audit: bool = False) -> Path:
    suffix = "Audit.lean" if audit else ".lean"
    return ROOT / "YangMills" / "RG" / f"{name}{suffix}"


def draft(name: str, *, audit: bool = False) -> Path:
    suffix = "Audit.draft.lean" if audit else ".draft.lean"
    return ROOT / "tmp" / f"{name}{suffix}"


def sealed_step8b23_content(path: Path) -> bytes:
    promoted = P23["transform"](path)[0].decode("utf-8")
    marker: str = P23["PRE_VALIDATION"]
    if promoted.count(marker) != 1:
        raise ValueError(f"unexpected Step8b23 PRE marker count: {path.name}")
    return promoted.replace(marker, "", 1).encode("utf-8")


def proposed_old_owner() -> bytes:
    old = OWNERSHIP["text"](OWNERSHIP["OLD"])
    old_start = old.index(OWNERSHIP["MARKER"])
    old_end = old.index(OWNERSHIP["NEXT_MARKER"], old_start)
    import_line = f"import {OWNERSHIP['NEW_MODULE']}\n"
    anchor = (
        "import YangMills.RG."
        "BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing\n"
    )
    if old.count(anchor) != 1 or import_line in old:
        raise ValueError("old-owner import boundary changed")
    proposed = old[:old_start] + old[old_end:]
    proposed = proposed.replace(anchor, anchor + import_line, 1)
    before = OWNERSHIP["DECL"].findall(old)
    after = OWNERSHIP["DECL"].findall(proposed)
    name = OWNERSHIP["NAME"]
    if before.count(name) != 1 or name in after:
        raise ValueError("ownership declaration was not moved exactly once")
    if [item for item in before if item != name] != after:
        raise ValueError("ownership move changes unrelated declaration order")
    return proposed.encode("utf-8")


def main() -> int:
    failures: list[str] = []

    first = [name for _, names in SCHEDULE["STEP8B23_SCHEDULE"] for name in names]
    extension = [name for _, name in SCHEDULE["STEP8B24_SCHEDULE"]]
    if len(first) != 22 or len(set(first)) != 22:
        failures.append("Step8b23 prerequisite schedule is not 22 unique modules")
    if len(extension) != 17 or len(set(extension)) != 17:
        failures.append("Step8b24 extension schedule is not 17 unique modules")
    if set(first) & set(extension):
        failures.append("Step8b23/Step8b24 module overlap")

    prerequisite_state: list[str] = []
    prerequisite_manifest: list[str] = []
    for name in first:
        for is_audit in (False, True):
            source = draft(name, audit=is_audit)
            tracked = target(name, audit=is_audit)
            try:
                expected = sealed_step8b23_content(source)
                prerequisite_manifest.append(
                    f"{sha(expected)}  {tracked.relative_to(ROOT).as_posix()}\n"
                )
                if tracked.exists():
                    prerequisite_state.append("present")
                    if tracked.read_bytes() != expected:
                        failures.append(
                            f"sealed Step8b23 prerequisite byte drift: {tracked.relative_to(ROOT)}"
                        )
                else:
                    prerequisite_state.append("absent")
            except (OSError, ValueError) as error:
                failures.append(str(error))
    present = prerequisite_state.count("present")
    absent = prerequisite_state.count("absent")
    if present not in (0, 44) or absent not in (0, 44):
        failures.append(f"partial Step8b23 prerequisite state present={present} absent={absent}")

    rows: list[str] = []
    declarations = 0
    imports_activated = 0
    for name in extension:
        for is_audit in (False, True):
            source = draft(name, audit=is_audit)
            tracked = target(name, audit=is_audit)
            try:
                if tracked.exists():
                    raise ValueError(f"extension target already exists: {tracked.relative_to(ROOT)}")
                content, activated, _inserted, _changes = P24["transform"](source)
                rows.append(f"{sha(content)}  {tracked.relative_to(ROOT).as_posix()}\n")
                imports_activated += activated
                if not is_audit:
                    declarations += len(P24["DECL"].findall(content.decode("utf-8")))
            except (OSError, ValueError) as error:
                failures.append(str(error))
    if declarations != 49:
        failures.append(f"extension declaration total {declarations}, expected 49")

    try:
        old_owner = proposed_old_owner()
        rows.append(
            f"{sha(old_owner)}  {OWNERSHIP['OLD'].relative_to(ROOT).as_posix()}\n"
        )
    except (OSError, ValueError) as error:
        failures.append(str(error))

    if failures:
        print("STEP8B24_EXTENSION_PROMOTION_PREVIEW_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    prerequisite_digest = hashlib.sha256(
        "".join(prerequisite_manifest).encode()
    ).hexdigest().upper()
    extension_digest = hashlib.sha256("".join(rows).encode()).hexdigest().upper()
    state = "ready" if present == 44 else "future"
    print(
        "STEP8B24_EXTENSION_PROMOTION_PREVIEW_OK "
        f"state={state} prerequisites_present={present} prerequisites_absent={absent} "
        f"new_files=34 modified_files=1 modules=17 declarations=49 "
        f"imports_activated={imports_activated} "
        f"prerequisite_manifest_sha256={prerequisite_digest} "
        f"extension_manifest_sha256={extension_digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
