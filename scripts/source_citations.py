#!/usr/bin/env python3
"""
Query the repository's structured primary-source citation catalog.

Examples:
  python scripts/source_citations.py list
  python scripts/source_citations.py show cmp116.eq231.p-bond-sum
  python scripts/source_citations.py excerpt cmp116.eq231.p-bond-sum
  python scripts/source_citations.py find Eq231
  python scripts/source_citations.py lean CMP116Eq231PBondBoundary
  python scripts/source_citations.py blockers
  python scripts/source_citations.py check-local
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any


DEFAULT_SOURCE_ROOT = Path(
    r"C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary"
)


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def catalog_dir() -> Path:
    return repo_root() / "docs" / "source-citations"


def source_db_catalog_dir() -> Path:
    return repo_root() / "docs" / "source-db" / "catalogs"


def catalog_paths() -> list[Path]:
    return sorted(catalog_dir().glob("*.json")) + sorted(source_db_catalog_dir().glob("*.json"))


def source_root() -> Path:
    env = os.environ.get("YM_SOURCE_ROOT")
    if env:
        return Path(env)
    return DEFAULT_SOURCE_ROOT


def local_text_hints(locator: dict[str, Any]) -> list[str]:
    value = locator.get("local_text")
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        return [str(item) for item in value]
    return []


def format_local_text(locator: dict[str, Any]) -> str:
    hints = local_text_hints(locator)
    return "; ".join(hints) if hints else "-"


def load_catalogs() -> tuple[dict[str, dict[str, Any]], list[dict[str, Any]]]:
    sources: dict[str, dict[str, Any]] = {}
    source_provenance: dict[str, Path] = {}
    citations: list[dict[str, Any]] = []
    for path in catalog_paths():
        data = json.loads(path.read_text(encoding="utf-8"))
        for source_id, source in data.get("sources", {}).items():
            if source_id not in sources:
                sources[source_id] = dict(source)
                source_provenance[source_id] = path
                continue
            merged = dict(sources[source_id])
            for key, value in dict(source).items():
                if key not in merged or merged[key] in (None, "", {}, []):
                    merged[key] = value
                elif value in (None, "", {}, []):
                    continue
                elif merged[key] != value:
                    raise SystemExit(
                        f"conflicting source metadata for {source_id}.{key}: "
                        f"{source_provenance[source_id]} vs {path}"
                    )
            sources[source_id] = merged
        for citation in data.get("citations", []):
            citation = dict(citation)
            citation["_catalog_file"] = str(path.relative_to(repo_root()))
            citations.append(citation)
    keys = [citation["key"] for citation in citations]
    duplicates = sorted({key for key in keys if keys.count(key) > 1})
    if duplicates:
        raise SystemExit("duplicate citation key(s): " + ", ".join(duplicates))
    return sources, citations


def citation_text(citation: dict[str, Any]) -> str:
    parts: list[str] = []
    for value in citation.values():
        if isinstance(value, str):
            parts.append(value)
        elif isinstance(value, list):
            parts.extend(str(item) for item in value)
        elif isinstance(value, dict):
            parts.extend(str(item) for item in value.values())
    return "\n".join(parts).lower()


def matching(citations: list[dict[str, Any]], term: str) -> list[dict[str, Any]]:
    needle = term.lower()
    return [citation for citation in citations if needle in citation_text(citation)]


def find_by_key(citations: list[dict[str, Any]], key: str) -> dict[str, Any]:
    for citation in citations:
        if citation["key"] == key:
            return citation
    raise SystemExit(f"unknown citation key: {key}")


def render_artifacts(
    citation: dict[str, Any], sources: dict[str, dict[str, Any]], check: bool = True
) -> list[tuple[str, Path | None, bool | None]]:
    source = sources.get(citation["source_id"], {})
    artifacts = source.get("local_artifacts", {})
    root = source_root()
    result: list[tuple[str, Path | None, bool | None]] = []

    # Always show the source PDF/text anchors first when present.
    artifact_names: list[str] = []
    for name in ("pdf", "text_full"):
        if name in artifacts:
            artifact_names.append(name)
    for name in citation.get("locator", {}).get("renders", []):
        if name in artifacts:
            artifact_names.append(name)
    for text_hint in local_text_hints(citation.get("locator", {})):
        text_name = text_hint.split()[0].replace("\\", "/")
        for name, rel in artifacts.items():
            rel_name = str(rel).replace("\\", "/")
            if (rel_name == text_name or rel_name.endswith("/" + text_name)) and name not in artifact_names:
                artifact_names.append(name)

    seen: set[str] = set()
    for name in artifact_names:
        if name in seen:
            continue
        seen.add(name)
        rel = artifacts.get(name)
        if not rel:
            result.append((name, None, None))
            continue
        path = root / rel
        result.append((name, path, path.exists() if check else None))
    return result


def local_text_excerpt_target_from_hint(
    citation: dict[str, Any], sources: dict[str, dict[str, Any]], text_hint: str
) -> tuple[Path, int | None, int | None]:
    file_hint = text_hint.split()[0].replace("\\", "/")
    line_match = re.search(r"\blines?\s+(\d+)(?:\s*[-–]\s*(\d+))?\b", text_hint)
    start = int(line_match.group(1)) if line_match else None
    end = int(line_match.group(2) or line_match.group(1)) if line_match else None
    if start is not None and end is not None and end < start:
        raise SystemExit(f"{citation['key']}: invalid line range in local_text: {text_hint}")

    source = sources.get(citation["source_id"], {})
    artifacts = source.get("local_artifacts", {})
    root = source_root()
    candidates: list[Path] = []
    for rel in artifacts.values():
        rel_name = str(rel).replace("\\", "/")
        if rel_name == file_hint or rel_name.endswith("/" + file_hint):
            candidates.append(root / rel)
    if not candidates:
        candidates.append(root / file_hint)
    repo_local = repo_root() / file_hint
    if repo_local.exists():
        candidates.insert(0, repo_local)

    existing = [path for path in candidates if path.exists()]
    if not existing:
        formatted = ", ".join(str(path) for path in candidates)
        raise SystemExit(f"{citation['key']}: local_text artifact not found: {formatted}")
    return existing[0], start, end


def local_text_excerpt_targets(
    citation: dict[str, Any], sources: dict[str, dict[str, Any]]
) -> list[tuple[Path, int | None, int | None]]:
    hints = local_text_hints(citation.get("locator", {}))
    if not hints:
        raise SystemExit(f"{citation['key']}: locator.local_text is missing")
    return [local_text_excerpt_target_from_hint(citation, sources, hint) for hint in hints]


def command_excerpt(args: argparse.Namespace) -> int:
    if args.context < 0:
        raise SystemExit("context must be nonnegative")
    sources, citations = load_catalogs()
    citation = find_by_key(citations, args.key)
    print(f"{citation['key']}")
    for index, (path, start, end) in enumerate(local_text_excerpt_targets(citation, sources)):
        if index:
            print()
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()

        if start is None or end is None:
            start = 1
            end = len(lines)
        start = max(1, start - args.context)
        end = min(len(lines), end + args.context)
        if start > len(lines):
            raise SystemExit(f"{citation['key']}: start line is past end of file: {path}")

        print(f"  source text: {path}")
        print(f"  lines: {start}-{end}")
        for line_no in range(start, end + 1):
            line = lines[line_no - 1]
            if args.no_line_numbers:
                print(line)
            else:
                print(f"{line_no:>5}: {line}")
    return 0


def url_items(value: Any) -> list[tuple[str, str]]:
    if isinstance(value, str):
        return [("", value)]
    if isinstance(value, list):
        return [("", str(item)) for item in value]
    if isinstance(value, dict):
        return [(str(name), str(url)) for name, url in value.items()]
    return []


def print_compact(citation: dict[str, Any], sources: dict[str, dict[str, Any]]) -> None:
    source = sources.get(citation["source_id"], {})
    locator = citation.get("locator", {})
    print(citation["key"])
    print(f"  source: {source.get('short', citation['source_id'])}")
    print(f"  status: {citation.get('status', 'unknown')}")
    print(f"  equations: {', '.join(locator.get('equations', [])) or '-'}")
    print(f"  printed pages: {locator.get('printed_pages', '-')}")
    print(f"  pdf pages: {locator.get('pdf_pages', '-')}")
    print(f"  local text: {format_local_text(locator)}")
    print(f"  summary: {citation.get('summary', '-')}")
    web_urls: list[tuple[str, str, str]] = []
    for name, url in url_items(source.get("web_urls")):
        web_urls.append(("source", name, url))
    for name, url in url_items(locator.get("web_urls")):
        web_urls.append(("locator", name, url))
    if web_urls:
        print("  web URLs:")
        seen_urls: set[str] = set()
        for scope, name, url in web_urls:
            if url in seen_urls:
                continue
            seen_urls.add(url)
            label = f"{scope}.{name}" if name else scope
            print(f"    - {label}: {url}")
    extracted_claims = citation.get("extracted_claims", [])
    if extracted_claims:
        print("  extracted claims:")
        for claim in extracted_claims:
            print(f"    - {claim}")
    targets = citation.get("lean_targets", [])
    if targets:
        print("  Lean targets:")
        for target in targets:
            print(f"    - {target}")
    use_for = citation.get("use_for", [])
    if use_for:
        print("  use for:")
        for item in use_for:
            print(f"    - {item}")
    do_not_use_for = citation.get("do_not_use_for", [])
    if do_not_use_for:
        print("  do not use for:")
        for item in do_not_use_for:
            print(f"    - {item}")
    dictionary_links = citation.get("dictionary_links", [])
    if dictionary_links:
        print("  dictionary links:")
        for link in dictionary_links:
            source_symbol = link.get("source_symbol", "-")
            lean_symbol = link.get("lean_symbol", "-")
            relation = link.get("relation", "-")
            status = link.get("status", "-")
            print(f"    - {source_symbol} -> {lean_symbol} ({relation}; {status})")
    open_questions = citation.get("open_questions", [])
    if open_questions:
        print("  open questions:")
        for question in open_questions:
            print(f"    - {question}")
    artifacts = render_artifacts(citation, sources)
    if artifacts:
        print("  local artifacts:")
        for name, path, exists in artifacts:
            marker = "ok" if exists else "missing" if exists is False else "?"
            print(f"    - {name}: {path} [{marker}]")


def command_list(args: argparse.Namespace) -> int:
    sources, citations = load_catalogs()
    for citation in citations:
        source = sources.get(citation["source_id"], {})
        print(
            f"{citation['key']}\t{citation.get('status', 'unknown')}\t"
            f"{source.get('short', citation['source_id'])}\t{citation.get('summary', '')}"
        )
    return 0


def command_show(args: argparse.Namespace) -> int:
    sources, citations = load_catalogs()
    citation = find_by_key(citations, args.key)
    if args.format == "json":
        print(json.dumps(citation, indent=2, sort_keys=True))
    else:
        print_compact(citation, sources)
    return 0


def command_find(args: argparse.Namespace) -> int:
    sources, citations = load_catalogs()
    hits = matching(citations, args.term)
    if not hits:
        return 1
    for citation in hits:
        if args.verbose:
            print_compact(citation, sources)
        else:
            print(f"{citation['key']}\t{citation.get('status', 'unknown')}\t{citation.get('summary', '')}")
    return 0


def command_lean(args: argparse.Namespace) -> int:
    sources, citations = load_catalogs()
    hits = [
        citation
        for citation in citations
        if any(args.name.lower() in str(target).lower() for target in citation.get("lean_targets", []))
    ]
    if not hits:
        return 1
    for citation in hits:
        if args.verbose:
            print_compact(citation, sources)
        else:
            print(f"{citation['key']}\t{citation.get('status', 'unknown')}\t{citation.get('summary', '')}")
    return 0


def command_blockers(args: argparse.Namespace) -> int:
    sources, citations = load_catalogs()
    statuses = set(args.status or ["source_pending", "ocr_corrupted"])
    hits = [citation for citation in citations if citation.get("status") in statuses]
    if not hits:
        return 1
    for index, citation in enumerate(hits):
        if index:
            print()
        if args.verbose:
            print_compact(citation, sources)
            continue
        source = sources.get(citation["source_id"], {})
        print(
            f"{citation['key']}\t{citation.get('status', 'unknown')}\t"
            f"{source.get('short', citation['source_id'])}\t{citation.get('summary', '')}"
        )
        targets = citation.get("lean_targets", [])
        if targets:
            shown = ", ".join(str(target) for target in targets[:4])
            suffix = "" if len(targets) <= 4 else f", ... (+{len(targets) - 4})"
            print(f"  Lean targets: {shown}{suffix}")
        open_questions = citation.get("open_questions", [])
        if open_questions:
            print(f"  first open question: {open_questions[0]}")
    return 0


def command_check_local(args: argparse.Namespace) -> int:
    sources, citations = load_catalogs()
    missing = 0
    print(f"source root: {source_root()}")
    for citation in citations:
        for name, path, exists in render_artifacts(citation, sources):
            if path is None:
                continue
            if not exists:
                missing += 1
            marker = "ok" if exists else "missing"
            print(f"{marker}\t{citation['key']}\t{name}\t{path}")
    return 1 if missing else 0


def command_validate(args: argparse.Namespace) -> int:
    sources, citations = load_catalogs()
    errors: list[str] = []
    for citation in citations:
        if citation.get("source_id") not in sources:
            errors.append(f"{citation.get('key')}: unknown source_id {citation.get('source_id')}")
        for field in ("key", "source_id", "status", "summary", "locator"):
            if field not in citation:
                errors.append(f"{citation.get('key', '<missing-key>')}: missing {field}")
        if citation.get("status") in {"lean_linked", "theorem_checked"} and not citation.get("lean_targets"):
            errors.append(f"{citation.get('key', '<missing-key>')}: missing lean_targets")
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    print(f"validated {len(citations)} citations from {len(sources)} sources")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    p_list = sub.add_parser("list", help="list citation keys")
    p_list.set_defaults(func=command_list)

    p_show = sub.add_parser("show", help="show one citation")
    p_show.add_argument("key")
    p_show.add_argument("--format", choices=["compact", "json"], default="compact")
    p_show.set_defaults(func=command_show)

    p_excerpt = sub.add_parser("excerpt", help="print the local text excerpt for one citation")
    p_excerpt.add_argument("key")
    p_excerpt.add_argument(
        "-C",
        "--context",
        type=int,
        default=0,
        help="number of context lines to include before and after the cited range",
    )
    p_excerpt.add_argument("--no-line-numbers", action="store_true")
    p_excerpt.set_defaults(func=command_excerpt)

    p_find = sub.add_parser("find", help="search citation text")
    p_find.add_argument("term")
    p_find.add_argument("-v", "--verbose", action="store_true")
    p_find.set_defaults(func=command_find)

    p_lean = sub.add_parser("lean", help="search by Lean target/declaration")
    p_lean.add_argument("name")
    p_lean.add_argument("-v", "--verbose", action="store_true")
    p_lean.set_defaults(func=command_lean)

    p_blockers = sub.add_parser(
        "blockers",
        help="list citation entries that are not theorem-feedable yet",
    )
    p_blockers.add_argument(
        "--status",
        action="append",
        choices=["source_pending", "ocr_corrupted", "visual_confirmed", "source_extracted"],
        help="status to include; repeat for multiple statuses",
    )
    p_blockers.add_argument("-v", "--verbose", action="store_true")
    p_blockers.set_defaults(func=command_blockers)

    p_check = sub.add_parser("check-local", help="check local source artifact paths")
    p_check.set_defaults(func=command_check_local)

    p_validate = sub.add_parser("validate", help="validate catalog structure")
    p_validate.set_defaults(func=command_validate)

    return parser


def main(argv: list[str] | None = None) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
