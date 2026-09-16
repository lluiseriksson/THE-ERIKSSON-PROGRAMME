#!/usr/bin/env python3
"""Read-only A--E / F split gate for the Step 8b.23 promotion."""

from __future__ import annotations

import hashlib
from pathlib import Path

import audit_step8b23_promotion_preview as preview


ROOT = Path(__file__).resolve().parents[1]
AE_PATHS = ROOT / "tmp" / "STEP8B23-UNIT-E-PREFIX-PATHS.txt"
F_PATHS = ROOT / "tmp" / "STEP8B23-UNIT-F-EXTENSION-PATHS.txt"


def listed(path: Path) -> list[Path]:
    return [
        ROOT / raw.strip()
        for raw in path.read_text(encoding="utf-8-sig").splitlines()
        if raw.strip() and not raw.lstrip().startswith("#")
    ]


def group_digest(label: str, drafts: list[Path]) -> tuple[str, int, int, int]:
    rows: list[str] = []
    sources = 0
    audits = 0
    declarations = 0
    for draft in drafts:
        content, _ = preview.transform(draft)
        target = preview.target_of(draft)
        rows.append(
            f"{hashlib.sha256(content).hexdigest()}  "
            f"{target.relative_to(ROOT).as_posix()}\n"
        )
        declarations += len(preview.DECL.findall(content.decode("utf-8")))
        if draft.name.endswith("Audit.draft.lean"):
            audits += 1
        else:
            sources += 1
    digest = hashlib.sha256("".join(rows).encode("utf-8")).hexdigest().upper()
    print(
        f"STEP8B23_{label}_PROMOTION_PREVIEW_OK files={len(drafts)} "
        f"sources={sources} audits={audits} declarations={declarations} "
        f"promoted_content_manifest_sha256={digest}"
    )
    return digest, sources, audits, declarations


def main() -> int:
    all_paths = preview.listed()
    ae = listed(AE_PATHS)
    unit_f = listed(F_PATHS)
    if len(ae) != 36 or len(unit_f) != 8:
        raise SystemExit(
            f"STEP8B23_SPLIT_PREVIEW_FAIL counts={len(ae)}/{len(unit_f)}"
        )
    if set(ae) & set(unit_f):
        raise SystemExit("STEP8B23_SPLIT_PREVIEW_FAIL overlap")
    if ae + unit_f != all_paths:
        raise SystemExit("STEP8B23_SPLIT_PREVIEW_FAIL ordered_union")

    _, ae_sources, ae_audits, ae_declarations = group_digest("AE", ae)
    _, f_sources, f_audits, f_declarations = group_digest("F", unit_f)
    if (ae_sources + f_sources, ae_audits + f_audits,
        ae_declarations + f_declarations) != (22, 22, 173):
        raise SystemExit("STEP8B23_SPLIT_PREVIEW_FAIL aggregate")
    print(
        "STEP8B23_SPLIT_PROMOTION_PREVIEW_OK "
        "ae_files=36 f_files=8 union=44 overlap=0 declarations=173"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
