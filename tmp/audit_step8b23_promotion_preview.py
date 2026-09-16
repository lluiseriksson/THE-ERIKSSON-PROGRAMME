#!/usr/bin/env python3
"""Read-only deterministic preview of the 44-file Step 8b.23 promotion.

No file is written.  The preview activates the sibling audit import when it
is still commented and inserts the mandated module docstring after the last
Lean import.  All declaration text is otherwise byte-preserved (modulo LF
normalization already used by the scratch manifests).
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
PATHS = TMP / "STEP8B23-ALL-PATHS.txt"
PRE_VALIDATION = (
    "/-!\n"
    "PRE-VALIDATION: this module's source is present, its `.olean` has not yet\n"
    "been materialized, and its result has not yet been verified by the compiler.\n"
    "-/\n"
)
IMPORT = re.compile(r"^import\s+([^\s]+)\s*$")
COMMENT_IMPORT = re.compile(r"^--\s*import\s+([^\s]+)\s*$")
DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)


def listed() -> list[Path]:
    return [
        ROOT / raw.strip()
        for raw in PATHS.read_text(encoding="utf-8-sig").splitlines()
        if raw.strip() and not raw.lstrip().startswith("#")
    ]


def target_of(draft: Path) -> Path:
    return ROOT / "YangMills" / "RG" / draft.name.replace(".draft.lean", ".lean")


def activate_audit_import(lines: list[str], draft: Path) -> tuple[list[str], bool]:
    if not draft.name.endswith("Audit.draft.lean"):
        return lines, False
    module = "YangMills.RG." + draft.name.removesuffix("Audit.draft.lean")
    active = [index for index, line in enumerate(lines) if IMPORT.match(line) and IMPORT.match(line).group(1) == module]
    commented = [
        index
        for index, line in enumerate(lines)
        if COMMENT_IMPORT.match(line) and COMMENT_IMPORT.match(line).group(1) == module
    ]
    if len(active) == 1 and not commented:
        return lines, False
    if not active and len(commented) == 1:
        result = list(lines)
        result[commented[0]] = f"import {module}"
        return result, True
    raise ValueError(
        f"ambiguous audit import {draft.name}: active={len(active)} commented={len(commented)}"
    )


def insert_pre_validation(lines: list[str], draft: Path) -> list[str]:
    if any("/-!" in line for line in lines):
        raise ValueError(f"pre-existing module docstring: {draft.name}")
    import_indices = [index for index, line in enumerate(lines) if IMPORT.match(line)]
    if not import_indices:
        raise ValueError(f"no active import after promotion: {draft.name}")
    last = max(import_indices)
    # A module docstring before any later import recreates the syntax failure
    # that previously consumed a cold session.
    if any(IMPORT.match(line) for line in lines[last + 1 :]):
        raise ValueError(f"non-final import insertion point: {draft.name}")
    insertion = PRE_VALIDATION.rstrip("\n").splitlines()
    result = list(lines)
    result[last + 1 : last + 1] = [""] + insertion
    return result


def late_import_lines(text: str) -> list[int]:
    """Mirror scripts/check_lean_import_prefix.py over in-memory output."""
    comment_stack: list[bool] = []
    command_seen = False
    failures: list[int] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        visible: list[str] = []
        index = 0
        while index < len(line):
            if comment_stack:
                if line.startswith("/-", index):
                    comment_stack.append(line.startswith(("/-!", "/--"), index))
                    index += 2
                elif line.startswith("-/", index):
                    comment_stack.pop()
                    index += 2
                else:
                    index += 1
                continue
            if line.startswith("--", index):
                break
            if line.startswith("/-", index):
                is_doc = line.startswith(("/-!", "/--"), index)
                comment_stack.append(is_doc)
                command_seen = command_seen or is_doc
                index += 2
                continue
            visible.append(line[index])
            index += 1
        code = "".join(visible).strip()
        if not code or code == "prelude":
            continue
        if code == "import" or code.startswith("import "):
            if command_seen:
                failures.append(line_number)
        else:
            command_seen = True
    return failures


def transform(draft: Path) -> tuple[bytes, bool]:
    original = draft.read_text(encoding="utf-8-sig").replace("\r\n", "\n")
    lines, uncommented = activate_audit_import(original.splitlines(), draft)
    lines = insert_pre_validation(lines, draft)
    promoted = "\n".join(lines) + "\n"
    if DECL.findall(original) != DECL.findall(promoted):
        raise ValueError(f"declaration sequence changed: {draft.name}")
    if "import tmp." in promoted:
        raise ValueError(f"scratch import survives promotion: {draft.name}")
    first_doc = promoted.index("/-!")
    last_import = max(match.end() for match in re.finditer(r"(?m)^import\s+[^\s]+\s*$", promoted))
    if first_doc < last_import:
        raise ValueError(f"module docstring precedes an import: {draft.name}")
    late = late_import_lines(promoted)
    if late:
        raise ValueError(f"late imports after preview in {draft.name}: {late}")
    return promoted.encode("utf-8"), uncommented


def main() -> int:
    failures: list[str] = []
    drafts = listed()
    if len(drafts) != 44 or len(set(drafts)) != 44:
        failures.append(f"scope={len(drafts)}/{len(set(drafts))}; expected 44/44")
    target_seen: set[Path] = set()
    manifest: list[str] = []
    uncommented_count = 0
    source_count = 0
    audit_count = 0
    declaration_count = 0

    for draft in drafts:
        try:
            if not draft.is_file():
                raise ValueError(f"missing draft: {draft.relative_to(ROOT)}")
            target = target_of(draft)
            if target in target_seen:
                raise ValueError(f"duplicate target: {target.relative_to(ROOT)}")
            target_seen.add(target)
            if target.exists():
                raise ValueError(f"tracked target already exists: {target.relative_to(ROOT)}")
            content, uncommented = transform(draft)
            declaration_count += len(DECL.findall(content.decode("utf-8")))
            uncommented_count += int(uncommented)
            if draft.name.endswith("Audit.draft.lean"):
                audit_count += 1
            else:
                source_count += 1
            manifest.append(
                f"{hashlib.sha256(content).hexdigest()}  {target.relative_to(ROOT).as_posix()}\n"
            )
        except (OSError, ValueError) as error:
            failures.append(str(error))

    if failures:
        print("STEP8B23_PROMOTION_PREVIEW_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    digest = hashlib.sha256("".join(manifest).encode("utf-8")).hexdigest().upper()
    print(
        "STEP8B23_PROMOTION_PREVIEW_OK "
        f"files={len(drafts)} sources={source_count} audits={audit_count} "
        f"audit_imports_activated={uncommented_count} "
        f"declaration_files_unchanged=44 declarations={declaration_count} "
        "import_prefix_ok=44 "
        f"promoted_content_manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
