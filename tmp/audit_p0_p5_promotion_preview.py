#!/usr/bin/env python3
"""Read-only deterministic promotion preview for the C6c.2 P0--P5 chain.

The preview never writes under ``YangMills/``.  It computes the exact promoted
bytes after three mechanical operations only:

* map each scratch source/audit to its declared tracked module path;
* rewrite ``tmp.*`` imports and provisional declaration identifiers; and
* replace scratch-only status prose by one removable PRE-VALIDATION paragraph.

Semantic Lean code is checked against an independently transformed visible-code
view, so comment cleanup cannot hide an accidental source edit.
"""

from __future__ import annotations

import hashlib
import importlib.util
import re
from pathlib import Path

import audit_p0_p5_promotion as scope


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
RG = ROOT / "YangMills" / "RG"
PATHS = TMP / "P0-P5-SCRATCH-PATHS.txt"
RAW_MANIFEST = TMP / "P0-P5-SCRATCH-MANIFEST.sha256"
EXPECTED_RAW_MANIFEST_SHA256 = (
    "A3FE74746D86909E6C7AD1980F1E05EF7E369F44A3456ACCD163A57C716AF885"
)
STANDARD_BODY = (
    "PRE-VALIDATION: this module's source is present, its `.olean` has not yet\n"
    "been materialized, and its result has not yet been verified by the compiler."
)
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)\s*$")
DECL = scope.DECL
PRIVATE_DECL = re.compile(
    r"(?m)^private\s+(?:noncomputable\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.]+)"
)
# A qualified occurrence is normally preceded by the namespace separator
# ``.``.  Dot therefore cannot be part of the boundary exclusion here, even
# though some declarations themselves contain a namespace-qualified name.
IDENT_CHARS = r"A-Za-z0-9_'’"
STATUS_SIGNALS = (
    "outside the tracked import graph",
    "compiler evidence",
    "compiler-verified",
    "imported by the tracked tree",
    "elaborated against the pinned toolchain",
)


def load_helpers():
    path = ROOT / "tmp" / "audit_step8b24_promotion_preview.py"
    spec = importlib.util.spec_from_file_location("step8b24_preview_helpers", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load Step 8b.24 preview helpers")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.VISIBLE_LINES, module.late_import_lines


VISIBLE_LINES, LATE_IMPORT_LINES = load_helpers()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def source_target_map() -> dict[Path, Path]:
    return {
        TMP / scratch: RG / tracked
        for scratch, tracked in scope.SOURCES
    }


def complete_target_map() -> dict[Path, Path]:
    result: dict[Path, Path] = {}
    for source, target in source_target_map().items():
        result[source] = target
        result[TMP / f"{source.stem}Audit.lean"] = target.with_name(
            f"{target.stem}Audit.lean"
        )
    result[TMP / "P3PhysicalGreenRecurrenceAggregateAudit.lean"] = (
        RG / "BalabanCMP85Eq241Eq242PhysicalGreenRecurrenceAggregateAudit.lean"
    )
    return result


def module_name(path: Path) -> str:
    return path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")


def declaration_map() -> dict[str, str]:
    result: dict[str, str] = {}
    for source in source_target_map():
        text = source.read_text(encoding="utf-8-sig")
        for old in (*DECL.findall(text), *PRIVATE_DECL.findall(text)):
            new = scope.promoted_name(old)
            if old in result and result[old] != new:
                raise ValueError(f"inconsistent declaration mapping: {old}")
            result[old] = new
    return result


def verify_raw_scope(listed: list[Path]) -> None:
    manifest_bytes = RAW_MANIFEST.read_bytes()
    measured = sha256(manifest_bytes)
    if measured != EXPECTED_RAW_MANIFEST_SHA256:
        raise ValueError(
            f"raw manifest digest drift: expected={EXPECTED_RAW_MANIFEST_SHA256} "
            f"actual={measured}"
        )
    rows: list[tuple[str, str]] = []
    for line in manifest_bytes.decode("utf-8").splitlines():
        parts = line.split("  ", 1)
        if len(parts) != 2 or not re.fullmatch(r"[0-9a-f]{64}", parts[0]):
            raise ValueError(f"malformed raw manifest row: {line}")
        rows.append((parts[1], parts[0]))
    expected_paths = [path.relative_to(ROOT).as_posix() for path in listed]
    if [path for path, _ in rows] != expected_paths:
        raise ValueError("raw manifest path/order drift")
    for relative, expected in rows:
        candidate = ROOT / relative
        actual = hashlib.sha256(candidate.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(
                f"raw manifest byte drift: {relative} expected={expected} actual={actual}"
            )


def rewrite_identifiers(text: str, names: dict[str, str]) -> str:
    changed = text
    for old in sorted(names, key=len, reverse=True):
        new = names[old]
        pattern = rf"(?<![{IDENT_CHARS}]){re.escape(old)}(?![{IDENT_CHARS}])"
        changed = re.sub(pattern, new, changed)
    return changed


def rewrite_imports(text: str, targets: dict[Path, Path]) -> str:
    imports = {
        module_name(source): module_name(target)
        for source, target in source_target_map().items()
    }

    def replace(match: re.Match[str]) -> str:
        imported = match.group(1)
        return f"import {imports.get(imported, imported)}"

    return IMPORT.sub(replace, text)


def clean_semantic_docstring(text: str, path: Path) -> str:
    starts = [match.start() for match in re.finditer(r"/-!", text)]
    if not starts:
        raise ValueError(f"module docstring missing: {path.name}")
    start = starts[0]
    end = text.find("-/", start)
    if end < 0:
        raise ValueError(f"unterminated module docstring: {path.name}")
    body = text[start + 3 : end].strip()
    body = body.replace("Scratch-only ", "").replace("scratch-only ", "")

    cleaned_paragraphs: list[str] = []
    for paragraph in re.split(r"\n\s*\n", body):
        sentences = re.split(r"(?<=[.!?])\s+", " ".join(paragraph.split()))
        kept = [
            sentence
            for sentence in sentences
            if sentence and not any(signal in sentence for signal in STATUS_SIGNALS)
        ]
        if kept:
            cleaned_paragraphs.append(" ".join(kept))
    if not cleaned_paragraphs:
        # Some scratch audits carry a governance-only PRE-VALIDATION module
        # docstring followed by the semantic audit docstring.  Promotion
        # removes the empty status block and normalizes the next module
        # docstring; it must not invent prose merely to keep the first block.
        return clean_semantic_docstring(text[:start] + text[end + 2 :], path)
    semantic = "\n\n".join(cleaned_paragraphs)
    replacement = f"/-!\n{semantic}\n\n{STANDARD_BODY}\n-/"
    return text[:start] + replacement + text[end + 2 :]


def transform(
    source: Path, targets: dict[Path, Path], names: dict[str, str]
) -> tuple[bytes, int]:
    original = source.read_text(encoding="utf-8-sig").replace("\r\n", "\n")
    expected_code_text = rewrite_identifiers(rewrite_imports(original, targets), names)
    promoted = clean_semantic_docstring(expected_code_text, source)
    if not promoted.endswith("\n"):
        promoted += "\n"

    expected_code = [line for line in VISIBLE_LINES(expected_code_text) if line.strip()]
    promoted_code = [line for line in VISIBLE_LINES(promoted) if line.strip()]
    if expected_code != promoted_code:
        raise ValueError(f"visible code changed during status normalization: {source.name}")
    if promoted.count(STANDARD_BODY) != 1:
        raise ValueError(f"standard PRE-VALIDATION count != 1: {source.name}")
    if any(signal in promoted for signal in STATUS_SIGNALS):
        raise ValueError(f"stale scratch status survives: {source.name}")
    if "Scratch-only" in promoted or "scratch-only" in promoted:
        raise ValueError(f"scratch-only label survives: {source.name}")
    if re.search(r"(?m)^import\s+tmp\.", promoted):
        raise ValueError(f"tmp import survives: {source.name}")
    provisional = [name for name in DECL.findall(promoted) if name != scope.promoted_name(name)]
    if provisional:
        raise ValueError(f"provisional declaration survives {source.name}: {provisional}")
    if re.search(r"(?<![A-Za-z0-9_])(?:scratch_|Scratch[A-Z])", promoted):
        raise ValueError(f"provisional identifier reference survives: {source.name}")
    late = LATE_IMPORT_LINES(promoted)
    if late:
        raise ValueError(f"late imports after promotion {source.name}: {late}")
    return promoted.encode("utf-8"), len(DECL.findall(promoted))


def main() -> int:
    failures: list[str] = []
    targets = complete_target_map()
    names = declaration_map()
    listed = [
        ROOT / line
        for line in PATHS.read_text(encoding="utf-8-sig").splitlines()
        if line
    ]
    try:
        verify_raw_scope(listed)
    except (OSError, UnicodeError, ValueError) as error:
        failures.append(str(error))
    if set(listed) != set(targets) or len(listed) != len(targets):
        failures.append(
            f"scope mismatch listed={len(listed)}/{len(set(listed))} "
            f"mapped={len(targets)}/{len(set(targets))}"
        )
    if len(set(targets.values())) != len(targets):
        failures.append("promoted target collision")

    manifest: list[str] = []
    promoted_texts: dict[Path, str] = {}
    declaration_total = 0
    for source in listed:
        try:
            if source not in targets:
                raise ValueError(f"unmapped scratch file: {source.relative_to(ROOT)}")
            target = targets[source]
            if target.exists():
                raise ValueError(f"tracked target already exists: {target.relative_to(ROOT)}")
            content, declarations = transform(source, targets, names)
            promoted_texts[source] = content.decode("utf-8")
            declaration_total += declarations
            manifest.append(
                f"{hashlib.sha256(content).hexdigest()}  "
                f"{target.relative_to(ROOT).as_posix()}\n"
            )
        except (OSError, RuntimeError, ValueError) as error:
            failures.append(str(error))

    promoted_modules = {module_name(path) for path in targets.values()}
    for source, text in promoted_texts.items():
        for imported in IMPORT.findall(text):
            if not imported.startswith("YangMills.") or imported in promoted_modules:
                continue
            external = ROOT / Path(*imported.split(".")).with_suffix(".lean")
            if not external.is_file():
                failures.append(
                    f"unresolved promoted import {source.name}: {imported}"
                )

    for source, target in source_target_map().items():
        audit = TMP / f"{source.stem}Audit.lean"
        if source not in promoted_texts or audit not in promoted_texts:
            continue
        declarations = DECL.findall(promoted_texts[source])
        prints = scope.PRINT.findall(promoted_texts[audit])
        if prints != declarations:
            failures.append(
                f"promoted sibling audit order/scope mismatch {source.name}: "
                f"expected={declarations} actual={prints}"
            )
        expected_imports = [module_name(target)]
        actual_imports = IMPORT.findall(promoted_texts[audit])
        if actual_imports != expected_imports:
            failures.append(
                f"promoted sibling audit import mismatch {audit.name}: "
                f"expected={expected_imports} actual={actual_imports}"
            )

    aggregate = TMP / "P3PhysicalGreenRecurrenceAggregateAudit.lean"
    p3_source = TMP / "P3PhysicalGreenRecurrence.lean"
    if aggregate in promoted_texts and p3_source in targets:
        expected_prints = [names[name] for name in scope.P3_AGGREGATE]
        actual_prints = scope.PRINT.findall(promoted_texts[aggregate])
        if actual_prints != expected_prints:
            failures.append(
                "promoted aggregate P3 readout drift: "
                f"expected={expected_prints} actual={actual_prints}"
            )
        expected_imports = [module_name(targets[p3_source])]
        actual_imports = IMPORT.findall(promoted_texts[aggregate])
        if actual_imports != expected_imports:
            failures.append(
                "promoted aggregate P3 import drift: "
                f"expected={expected_imports} actual={actual_imports}"
            )

    if declaration_total != 156:
        failures.append(f"declaration total {declaration_total}, expected 156")
    if failures:
        print("P0_P5_PROMOTION_PREVIEW_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    manifest_bytes = "".join(manifest).encode("utf-8")
    print(
        "P0_P5_PROMOTION_PREVIEW_OK "
        f"files={len(listed)} sources={len(scope.SOURCES)} sibling_audits={len(scope.SOURCES)} "
        f"aggregate_audits=1 declarations={declaration_total} renamed={len(names)} "
        f"pre_validation_blocks={len(listed)} promoted_imports_resolved=33 "
        f"sibling_audit_scopes=16 aggregate_audit_scopes=1 target_collisions=0 "
        f"promoted_content_manifest_sha256={sha256(manifest_bytes)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
