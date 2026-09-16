#!/usr/bin/env python3
"""Read-only audit of the Step 8b.24 neutral-theorem ownership move."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RG = ROOT / "YangMills" / "RG"
TMP = ROOT / "tmp"
NAME = "cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral"
OLD = RG / "BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentification.lean"
OLD_AUDIT = RG / "BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentificationAudit.lean"
NEW = TMP / "BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral.draft.lean"
NEW_AUDIT = TMP / "BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentralAudit.draft.lean"
SEPARATED = TMP / "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentification.draft.lean"
NEW_MODULE = "YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral"
MARKER = "/-- At zero mass, every noncentral entry of every literal physical"
NEXT_MARKER = "/-- Generated physical endpoint:"
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)


def text(path: Path) -> str:
    return path.read_text(encoding="utf-8-sig").replace("\r\n", "\n")


def sha(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest().upper()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def canonical(value: str) -> str:
    return value.rstrip() + "\n"


def main() -> int:
    try:
        old = text(OLD)
        new = text(NEW)
        old_start = old.index(MARKER)
        old_end = old.index(NEXT_MARKER, old_start)
        new_start = new.index(MARKER)
        new_end = new.index("\n\nend\n\nend YangMills.RG", new_start)
        old_block = canonical(old[old_start:old_end])
        new_block = canonical(new[new_start:new_end])
        require(old_block == new_block, "old/new theorem blocks differ")
        require(DECL.findall(new) == [NAME], "neutral draft does not own exactly the moved theorem")

        import_line = f"import {NEW_MODULE}\n"
        require(import_line not in old, "neutral import already present in old owner")
        insertion_anchor = (
            "import YangMills.RG."
            "BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing\n"
        )
        require(old.count(insertion_anchor) == 1, "old-owner import anchor is not unique")
        proposed = old[:old_start] + old[old_end:]
        proposed = proposed.replace(insertion_anchor, insertion_anchor + import_line, 1)

        before = DECL.findall(old)
        after = DECL.findall(proposed)
        require(before.count(NAME) == 1, "old owner lacks unique theorem declaration")
        require(NAME not in after, "old owner still declares moved theorem")
        require([item for item in before if item != NAME] == after, "unrelated declaration order changed")
        require(proposed.index(import_line) < proposed.index("/-!"), "new import would be late")
        require(proposed.count(NAME) >= 1, "old consumer no longer references imported theorem")

        old_audit = text(OLD_AUDIT)
        new_audit = text(NEW_AUDIT)
        separated = text(SEPARATED)
        print_line = f"#print axioms YangMills.RG.{NAME}"
        require(print_line in old_audit, "existing diagonal audit stops printing moved theorem")
        require(print_line in new_audit, "neutral sibling audit does not print moved theorem")
        require(
            f"-- import {NEW_MODULE}" in separated,
            "source-separated consumer lacks explicit neutral promotion import",
        )
        require(
            "BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentification" not in separated,
            "source-separated consumer imports the diagonal owner",
        )

        print(
            "STEP8B24_OWNERSHIP_MOVE_STATIC_OK "
            f"theorem={NAME} block_lines={len(old_block.splitlines())} "
            f"block_sha256={sha(old_block)} proposed_old_owner_sha256={sha(proposed)} "
            f"old_audit=retained neutral_audit=present separated_consumer=explicit"
        )
        return 0
    except (OSError, ValueError) as error:
        print(f"STEP8B24_OWNERSHIP_MOVE_STATIC_FAIL: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
