#!/usr/bin/env python3
"""Read-only deterministic preview of all 78 new Step 8b.23/8b.24 blobs."""

from __future__ import annotations

import hashlib
import importlib.util
import re
from pathlib import Path

from audit_step8b23_promotion_preview import late_import_lines


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
PATHS = TMP / "STEP8B24-ALL-PATHS.txt"
STANDARD_BODY = (
    "PRE-VALIDATION: this module's source is present, its `.olean` has not yet\n"
    "been materialized, and its result has not yet been verified by the compiler."
)
STANDARD_DOC = f"/-!\n{STANDARD_BODY}\n-/\n"
STALE_BODY = (
    "PRE-VALIDATION SCRATCH: this source is present only under `tmp`; no `.olean`\n"
    "has been materialized and no result in this file has been compiler-verified."
)
IMPORT = re.compile(r"^import\s+([^\s]+)\s*$")
COMMENT_IMPORT = re.compile(r"^--\s*import\s+([^\s]+)\s*$")
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)


def load_visible_lines():
    path = ROOT / "scripts" / "check_lean_overlay_text.py"
    spec = importlib.util.spec_from_file_location("step8b24_overlay_guard", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load overlay guard")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.visible_lines


VISIBLE_LINES = load_visible_lines()


def listed() -> list[Path]:
    return [
        ROOT / raw.strip()
        for raw in PATHS.read_text(encoding="utf-8-sig").splitlines()
        if raw.strip() and not raw.lstrip().startswith("#")
    ]


def activate_imports(text: str) -> tuple[str, int]:
    lines = text.splitlines()
    activated = 0
    for index, line in enumerate(lines):
        match = COMMENT_IMPORT.match(line)
        if match:
            lines[index] = f"import {match.group(1)}"
            activated += 1
    return "\n".join(lines) + "\n", activated


def normalize_status_comments(text: str) -> tuple[str, int]:
    changes = 0
    if STALE_BODY in text:
        text = text.replace(STALE_BODY, STANDARD_BODY)
        changes += 1
    replacements = (
        ("STATIC AUDIT DRAFT ONLY -- target module is not compiler-verified.",
         "PRE-VALIDATION AUDIT -- target module is not yet compiler-verified."),
        ("STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.",
         "PRE-VALIDATION SOURCE -- NOT YET COMPILER-VERIFIED."),
        ("PRE-VALIDATION SCRATCH:", "PRE-VALIDATION:"),
    )
    for old, new in replacements:
        count = text.count(old)
        text = text.replace(old, new)
        changes += count
    text, count = re.subn(r"\bThis scratch\s+file\b", "This module", text)
    changes += count
    return text, changes


def ensure_module_docstring(text: str, draft: Path) -> tuple[str, bool]:
    count = text.count("/-!")
    if count > 1:
        raise ValueError(f"multiple module docstrings: {draft.name}")
    if count == 1:
        if STANDARD_BODY not in text:
            raise ValueError(f"existing module docstring lacks standard status: {draft.name}")
        return text, False
    lines = text.splitlines()
    imports = [index for index, line in enumerate(lines) if IMPORT.match(line)]
    if not imports:
        raise ValueError(f"no import in promoted preview: {draft.name}")
    insertion = STANDARD_DOC.rstrip("\n").splitlines()
    last = max(imports)
    lines[last + 1 : last + 1] = [""] + insertion
    return "\n".join(lines) + "\n", True


def transform(draft: Path) -> tuple[bytes, int, bool, int]:
    original = draft.read_text(encoding="utf-8-sig").replace("\r\n", "\n")
    activated_text, activated = activate_imports(original)
    normalized, status_changes = normalize_status_comments(activated_text)
    promoted, inserted = ensure_module_docstring(normalized, draft)

    if COMMENT_IMPORT.search(promoted):
        raise ValueError(f"commented promotion import survives: {draft.name}")
    if STALE_BODY in promoted or "DRAFT ONLY" in promoted:
        raise ValueError(f"stale promotion status survives: {draft.name}")
    if promoted.count(STANDARD_BODY) != 1:
        raise ValueError(f"standard PRE-VALIDATION status count != 1: {draft.name}")
    late = late_import_lines(promoted)
    if late:
        raise ValueError(f"late imports after promotion in {draft.name}: {late}")
    if DECL.findall(original) != DECL.findall(promoted):
        raise ValueError(f"declaration sequence changed: {draft.name}")
    # Apart from activating declared imports, promotion is comment-only.
    activated_code = [line for line in VISIBLE_LINES(activated_text) if line.strip()]
    promoted_code = [line for line in VISIBLE_LINES(promoted) if line.strip()]
    if activated_code != promoted_code:
        raise ValueError(f"non-comment code changed after import activation: {draft.name}")
    return promoted.encode("utf-8"), activated, inserted, status_changes


def main() -> int:
    failures: list[str] = []
    drafts = listed()
    if len(drafts) != 78 or len(set(drafts)) != 78:
        failures.append(f"scope={len(drafts)}/{len(set(drafts))}; expected 78/78")
    manifest: list[str] = []
    targets: set[Path] = set()
    activated_total = 0
    inserted_total = 0
    existing_docstrings = 0
    status_changes_total = 0
    declaration_total = 0

    for draft in drafts:
        try:
            if not draft.is_file():
                raise ValueError(f"missing draft: {draft.relative_to(ROOT)}")
            target = ROOT / "YangMills" / "RG" / draft.name.replace(".draft.lean", ".lean")
            if target in targets:
                raise ValueError(f"duplicate target: {target.relative_to(ROOT)}")
            targets.add(target)
            if target.exists():
                raise ValueError(f"tracked target already exists: {target.relative_to(ROOT)}")
            had_docstring = "/-!" in draft.read_text(encoding="utf-8-sig")
            content, activated, inserted, status_changes = transform(draft)
            activated_total += activated
            inserted_total += int(inserted)
            existing_docstrings += int(had_docstring)
            status_changes_total += status_changes
            declaration_total += len(DECL.findall(content.decode("utf-8")))
            manifest.append(
                f"{hashlib.sha256(content).hexdigest()}  {target.relative_to(ROOT).as_posix()}\n"
            )
        except (OSError, RuntimeError, ValueError) as error:
            failures.append(str(error))

    if declaration_total != 222:
        failures.append(f"declaration total {declaration_total}, expected 222")
    if failures:
        print("STEP8B24_PROMOTION_PREVIEW_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    digest = hashlib.sha256("".join(manifest).encode("utf-8")).hexdigest().upper()
    print(
        "STEP8B24_PROMOTION_PREVIEW_OK "
        f"files=78 declarations={declaration_total} imports_activated={activated_total} "
        f"docstrings_existing={existing_docstrings} docstrings_inserted={inserted_total} "
        f"status_comment_changes={status_changes_total} import_prefix_ok=78 "
        f"promoted_content_manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
