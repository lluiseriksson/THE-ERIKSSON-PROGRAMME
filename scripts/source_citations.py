#!/usr/bin/env python3
"""
Query the repository's structured primary-source citation catalog.

Examples:
  python scripts/source_citations.py list
  python scripts/source_citations.py show cmp116.eq231.p-bond-sum
  python scripts/source_citations.py find Eq231
  python scripts/source_citations.py lean CMP116Eq231PBondBoundary
  python scripts/source_citations.py check-local
"""

from __future__ import annotations

import argparse
import json
import os
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


def source_root() -> Path:
    env = os.environ.get("YM_SOURCE_ROOT")
    if env:
        return Path(env)
    return DEFAULT_SOURCE_ROOT


def load_catalogs() -> tuple[dict[str, dict[str, Any]], list[dict[str, Any]]]:
    sources: dict[str, dict[str, Any]] = {}
    citations: list[dict[str, Any]] = []
    for path in sorted(catalog_dir().glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        for source_id, source in data.get("sources", {}).items():
            if source_id in sources and sources[source_id] != source:
                raise SystemExit(f"conflicting source metadata for {source_id} in {path}")
            sources[source_id] = source
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
    text_hint = citation.get("locator", {}).get("local_text")
    if isinstance(text_hint, str):
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


def print_compact(citation: dict[str, Any], sources: dict[str, dict[str, Any]]) -> None:
    source = sources.get(citation["source_id"], {})
    locator = citation.get("locator", {})
    print(citation["key"])
    print(f"  source: {source.get('short', citation['source_id'])}")
    print(f"  status: {citation.get('status', 'unknown')}")
    print(f"  equations: {', '.join(locator.get('equations', [])) or '-'}")
    print(f"  printed pages: {locator.get('printed_pages', '-')}")
    print(f"  pdf pages: {locator.get('pdf_pages', '-')}")
    print(f"  local text: {locator.get('local_text', '-')}")
    print(f"  summary: {citation.get('summary', '-')}")
    targets = citation.get("lean_targets", [])
    if targets:
        print("  Lean targets:")
        for target in targets:
            print(f"    - {target}")
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
        for field in ("key", "source_id", "status", "summary", "locator", "lean_targets"):
            if field not in citation:
                errors.append(f"{citation.get('key', '<missing-key>')}: missing {field}")
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

    p_find = sub.add_parser("find", help="search citation text")
    p_find.add_argument("term")
    p_find.add_argument("-v", "--verbose", action="store_true")
    p_find.set_defaults(func=command_find)

    p_lean = sub.add_parser("lean", help="search by Lean target/declaration")
    p_lean.add_argument("name")
    p_lean.add_argument("-v", "--verbose", action="store_true")
    p_lean.set_defaults(func=command_lean)

    p_check = sub.add_parser("check-local", help="check local source artifact paths")
    p_check.set_defaults(func=command_check_local)

    p_validate = sub.add_parser("validate", help="validate catalog structure")
    p_validate.set_defaults(func=command_validate)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
