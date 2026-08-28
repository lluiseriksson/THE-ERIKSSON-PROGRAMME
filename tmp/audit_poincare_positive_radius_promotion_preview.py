#!/usr/bin/env python3
"""Read-only promotion preview for the positive-radius Poincare brick."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tmp" / "PoincarePositiveRadiusReachability.lean"
AUDIT = ROOT / "tmp" / "PoincarePositiveRadiusReachabilityAudit.lean"
SOURCE_TARGET = (
    ROOT / "YangMills" / "RG" /
    "BalabanCMP99SourcePoincarePositiveRadiusReachability.lean"
)
AUDIT_TARGET = (
    ROOT / "YangMills" / "RG" /
    "BalabanCMP99SourcePoincarePositiveRadiusReachabilityAudit.lean"
)
MODULE_DOC = (
    "/-!\n"
    "PRE-VALIDATION: this module's source is present, its `.olean` has not yet\n"
    "been materialized, and its result has not yet been verified by the compiler.\n"
    "-/\n"
)
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)
IMPORT = re.compile(r"(?m)^import\s+[^\s]+\s*$")


def insert_doc_after_imports(text: str) -> str:
    imports = list(IMPORT.finditer(text))
    if not imports:
        raise ValueError("no import")
    if "/-!" in text:
        raise ValueError("pre-existing module docstring")
    end = imports[-1].end()
    result = text[:end] + "\n\n" + MODULE_DOC.rstrip("\n") + text[end:]
    last_import = max(match.end() for match in IMPORT.finditer(result))
    if result.index("/-!") < last_import:
        raise ValueError("module docstring precedes an import")
    return result.rstrip("\n") + "\n"


def source_content() -> bytes:
    original = SOURCE.read_text(encoding="utf-8-sig").replace("\r\n", "\n")
    original = re.sub(
        r"\A/- PRE-VALIDATION scratch source\.\n"
        r"Source is present; no `\.olean` has been materialized and no declaration below\n"
        r"has been verified by the Lean compiler\. -/\n\n",
        "",
        original,
        count=1,
    )
    promoted = insert_doc_after_imports(original.replace("scratch_", ""))
    old_names = [name.removeprefix("scratch_") for name in DECL.findall(original)]
    new_names = DECL.findall(promoted)
    if old_names != new_names:
        raise ValueError(f"source declaration mismatch: {old_names} != {new_names}")
    if "scratch_" in promoted or "import tmp." in promoted:
        raise ValueError("scratch token survives source promotion")
    return promoted.encode("utf-8")


def audit_content() -> bytes:
    original = AUDIT.read_text(encoding="utf-8-sig").replace("\r\n", "\n")
    promoted = insert_doc_after_imports(original)
    if "scratch_" in promoted or "import tmp." in promoted:
        raise ValueError("scratch token survives audit promotion")
    expected = "import YangMills.RG.BalabanCMP99SourcePoincarePositiveRadiusReachability"
    if promoted.count(expected) != 1:
        raise ValueError("audit target import is not unique")
    source_names = DECL.findall(source_content().decode("utf-8"))
    audit_names = re.findall(
        r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_.'’]+)\s*$",
        promoted,
    )
    if source_names != audit_names:
        raise ValueError(f"audit declaration mismatch: {source_names} != {audit_names}")
    return promoted.encode("utf-8")


def main() -> int:
    for path in (SOURCE, AUDIT):
        if not path.is_file():
            raise SystemExit(f"POINCARE_PROMOTION_PREVIEW_FAIL missing={path}")
    for target in (SOURCE_TARGET, AUDIT_TARGET):
        if target.exists():
            raise SystemExit(f"POINCARE_PROMOTION_PREVIEW_FAIL target_exists={target}")

    source = source_content()
    audit = audit_content()
    rows = [
        (SOURCE_TARGET.relative_to(ROOT).as_posix(), hashlib.sha256(source).hexdigest()),
        (AUDIT_TARGET.relative_to(ROOT).as_posix(), hashlib.sha256(audit).hexdigest()),
    ]
    manifest = "".join(f"{digest}  {path}\n" for path, digest in rows)
    digest = hashlib.sha256(manifest.encode("utf-8")).hexdigest().upper()
    declarations = len(DECL.findall(source.decode("utf-8")))
    print(
        "POINCARE_PROMOTION_PREVIEW_OK "
        f"files=2 declarations={declarations} audits={declarations} "
        f"promoted_content_manifest_sha256={digest}"
    )
    for path, sha in rows:
        print(f"{sha.upper()}  {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
