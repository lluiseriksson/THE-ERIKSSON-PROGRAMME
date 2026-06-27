#!/usr/bin/env python3
"""Build and query THE-ERIKSSON-PROGRAMME's source/citation database.

The canonical records remain JSON. SQLite is a generated, fast lookup index.
Only Python's standard library is required.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import zipfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Iterator

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

VALID_STATUSES = {
    "discovered",
    "located",
    "visual_confirmed",
    "ocr_corrupted",
    "source_pending",
    "source_extracted",
    "lean_linked",
    "theorem_checked",
}
BLOCKING_STATUSES = {"discovered", "located", "ocr_corrupted", "source_pending"}
DEFAULT_WINDOWS_SOURCE_ROOT = Path(
    r"C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary"
)
FIXED_ZIP_TIME = (2026, 1, 1, 0, 0, 0)
GIT_COMMIT_REF = re.compile(
    r"\b(?:HEAD|head|Git commit|git commit|commit)\s+`?([0-9a-fA-F]{7,40})`?\b"
)


@dataclass(frozen=True)
class CatalogRecord:
    path: Path
    data: dict[str, Any]


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def source_root() -> Path:
    value = os.environ.get("YM_SOURCE_ROOT")
    return Path(value) if value else DEFAULT_WINDOWS_SOURCE_ROOT


def db_path() -> Path:
    return repo_root() / "docs" / "source-db" / "source_index.sqlite"


def json_text(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))




def normalize_search_text(value: str) -> str:
    """Normalize punctuation-heavy mathematical lookup terms for LIKE queries."""
    return " ".join(re.sub(r"[^a-z0-9]+", " ", value.lower()).split())


def run_git(root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def catalog_paths(root: Path | None = None) -> list[Path]:
    root = root or repo_root()
    legacy = sorted((root / "docs" / "source-citations").glob("*.json"))
    extended = sorted((root / "docs" / "source-db" / "catalogs").glob("*.json"))
    # The ZIP is independently runnable. In a real checkout, the repository's
    # existing docs/source-citations catalog wins and the example seed is skipped.
    examples: list[Path] = []
    if not legacy:
        examples = sorted((root / "docs" / "source-db" / "examples").glob("*.json"))
    return legacy + extended + examples


def load_catalogs(root: Path | None = None) -> list[CatalogRecord]:
    records: list[CatalogRecord] = []
    for path in catalog_paths(root):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise SystemExit(f"cannot load catalog {path}: {exc}") from exc
        if not isinstance(data, dict):
            raise SystemExit(f"catalog root must be an object: {path}")
        records.append(CatalogRecord(path=path, data=data))
    if not records:
        raise SystemExit("no source catalogs found")
    return records


def year_from_source(source: dict[str, Any]) -> int | None:
    for key in ("year", "journal", "title"):
        value = source.get(key)
        if isinstance(value, int):
            return value
        if isinstance(value, str):
            match = re.search(r"\b(18|19|20)\d{2}\b", value)
            if match:
                return int(match.group(0))
    return None


def merge_sources(records: Iterable[CatalogRecord]) -> dict[str, dict[str, Any]]:
    sources: dict[str, dict[str, Any]] = {}
    provenance: dict[str, Path] = {}
    for record in records:
        for source_id, source_value in record.data.get("sources", {}).items():
            if not isinstance(source_value, dict):
                raise SystemExit(f"{record.path}: source {source_id} must be an object")
            source = dict(source_value)
            if source_id not in sources:
                sources[source_id] = source
                provenance[source_id] = record.path
                continue
            merged = dict(sources[source_id])
            for key, value in source.items():
                if key not in merged or merged[key] in (None, "", {}, []):
                    merged[key] = value
                elif value in (None, "", {}, []):
                    continue
                elif merged[key] != value:
                    raise SystemExit(
                        f"conflicting source metadata for {source_id}.{key}: "
                        f"{provenance[source_id]} vs {record.path}"
                    )
            sources[source_id] = merged
    return sources


def iter_citations(records: Iterable[CatalogRecord], root: Path) -> Iterator[tuple[Path, dict[str, Any]]]:
    seen: dict[str, Path] = {}
    for record in records:
        for raw in record.data.get("citations", []):
            if not isinstance(raw, dict):
                raise SystemExit(f"{record.path}: citation must be an object")
            citation = dict(raw)
            key = citation.get("key")
            if not isinstance(key, str) or not key:
                raise SystemExit(f"{record.path}: citation key missing")
            if key in seen:
                raise SystemExit(f"duplicate citation key {key}: {seen[key]} and {record.path}")
            seen[key] = record.path
            yield record.path.relative_to(root), citation


def validate_catalogs(records: list[CatalogRecord], root: Path | None = None) -> list[str]:
    root = root or repo_root()
    errors: list[str] = []
    try:
        sources = merge_sources(records)
    except SystemExit as exc:
        return [str(exc)]

    citation_keys: set[str] = set()
    try:
        citations = list(iter_citations(records, root))
    except SystemExit as exc:
        return [str(exc)]

    for path, citation in citations:
        key = citation.get("key", "<missing>")
        citation_keys.add(str(key))
        source_id = citation.get("source_id")
        if source_id not in sources:
            errors.append(f"{path}: {key}: unknown source_id {source_id!r}")
        status = citation.get("status")
        if status not in VALID_STATUSES:
            errors.append(f"{path}: {key}: invalid status {status!r}")
        locator = citation.get("locator")
        if not isinstance(locator, dict):
            errors.append(f"{path}: {key}: locator must be an object")
        else:
            for page_field in ("printed_pages", "pdf_pages"):
                if page_field not in locator:
                    errors.append(f"{path}: {key}: locator.{page_field} missing")
        if not isinstance(citation.get("summary"), str) or not citation.get("summary"):
            errors.append(f"{path}: {key}: summary missing")
        formulas = citation.get("formulas", [])
        formula_ids: set[str] = set()
        if not isinstance(formulas, list):
            errors.append(f"{path}: {key}: formulas must be a list")
            formulas = []
        for index, formula in enumerate(formulas):
            if not isinstance(formula, dict):
                errors.append(f"{path}: {key}: formula #{index + 1} must be an object")
                continue
            formula_id = formula.get("id")
            if not isinstance(formula_id, str) or not formula_id:
                errors.append(f"{path}: {key}: formula #{index + 1} id missing")
            elif formula_id in formula_ids:
                errors.append(f"{path}: {key}: duplicate formula id {formula_id}")
            formula_ids.add(str(formula_id))
            if formula.get("source_verified") and formula.get("exactness") == "inferred":
                errors.append(f"{path}: {key}: inferred formula cannot be source_verified")
        if status in {"source_extracted", "lean_linked", "theorem_checked"}:
            if not formulas and not citation.get("extracted_claims"):
                errors.append(f"{path}: {key}: {status} requires extracted formula/claims")
        if status in {"lean_linked", "theorem_checked"} and not citation.get("lean_targets"):
            errors.append(f"{path}: {key}: {status} requires lean_targets")
        if status == "theorem_checked" and citation.get("open_questions"):
            # Not forbidden, but must be explicit because theorem_checked may only
            # concern one consumer, not the whole source claim.
            pass

    for record in records:
        for coverage in record.data.get("coverage", []):
            if not isinstance(coverage, dict):
                errors.append(f"{record.path}: coverage entry must be an object")
                continue
            if coverage.get("source_id") not in sources:
                errors.append(f"{record.path}: coverage unknown source {coverage.get('source_id')!r}")
    return errors


def ensure_schema(conn: sqlite3.Connection, root: Path) -> None:
    schema = (root / "docs" / "source-db" / "schema.sql").read_text(encoding="utf-8")
    conn.executescript(schema)


def artifact_media_type(path: str) -> str | None:
    suffix = Path(path).suffix.lower()
    return {
        ".pdf": "application/pdf",
        ".txt": "text/plain",
        ".png": "image/png",
        ".jpg": "image/jpeg",
        ".jpeg": "image/jpeg",
        ".json": "application/json",
    }.get(suffix)


def build_database(output: Path | None = None, root: Path | None = None) -> Path:
    root = root or repo_root()
    output = output or db_path()
    records = load_catalogs(root)
    errors = validate_catalogs(records, root)
    if errors:
        raise SystemExit("catalog validation failed:\n  - " + "\n  - ".join(errors))
    sources = merge_sources(records)
    citations = list(iter_citations(records, root))

    output.parent.mkdir(parents=True, exist_ok=True)
    fd, temp_name = tempfile.mkstemp(
        prefix=f"{output.name}.",
        suffix=".tmp",
        dir=output.parent,
    )
    os.close(fd)
    temp = Path(temp_name)
    temp.unlink(missing_ok=True)
    conn = sqlite3.connect(temp)
    conn.row_factory = sqlite3.Row
    try:
        ensure_schema(conn, root)
        conn.execute("INSERT OR REPLACE INTO meta(key,value) VALUES (?,?)", ("schema_version", "1"))
        conn.execute("INSERT OR REPLACE INTO meta(key,value) VALUES (?,?)", ("generated_from", json_text([str(p.relative_to(root)) for p in catalog_paths(root)])))
        conn.execute("INSERT OR REPLACE INTO meta(key,value) VALUES (?,?)", ("generator", "scripts/source_db.py"))

        for source_id in sorted(sources):
            source = sources[source_id]
            conn.execute(
                """INSERT INTO sources(source_id,short,title,author,journal,year,doi,status,license_note,metadata_json)
                   VALUES (?,?,?,?,?,?,?,?,?,?)""",
                (
                    source_id,
                    str(source.get("short", source_id)),
                    source.get("title"),
                    source.get("author"),
                    source.get("journal"),
                    year_from_source(source),
                    source.get("doi"),
                    source.get("status", "registered"),
                    source.get("license_note"),
                    json_text(source),
                ),
            )
            for artifact_name, relpath in sorted(source.get("local_artifacts", {}).items()):
                full = source_root() / str(relpath)
                exists = full.exists()
                conn.execute(
                    """INSERT INTO artifacts(source_id,artifact_name,relative_path,sha256,byte_size,media_type,public_commit_allowed,exists_local)
                       VALUES (?,?,?,?,?,?,?,?)""",
                    (
                        source_id,
                        artifact_name,
                        str(relpath).replace("\\", "/"),
                        sha256_file(full) if exists and full.is_file() else None,
                        full.stat().st_size if exists and full.is_file() else None,
                        artifact_media_type(str(relpath)),
                        0,
                        int(exists),
                    ),
                )

        for catalog_file, citation in citations:
            key = citation["key"]
            locator = citation.get("locator", {})
            local_text = locator.get("local_text", [])
            if isinstance(local_text, str):
                local_text = [local_text]
            search_parts = [
                key,
                str(citation.get("summary", "")),
                " ".join(f"eq {equation}" for equation in locator.get("equations", [])),
                " ".join(map(str, citation.get("extracted_claims", []))),
                " ".join(map(str, citation.get("lean_targets", []))),
                " ".join(map(str, citation.get("open_questions", []))),
            ]
            for formula in citation.get("formulas", []):
                search_parts.extend(
                    [str(formula.get("statement", "")), str(formula.get("ascii", "")), str(formula.get("latex", ""))]
                )
            conn.execute(
                """INSERT INTO citations(citation_key,source_id,catalog_file,status,summary,printed_pages,pdf_pages,locator_json,local_text_json,use_for_json,do_not_use_for_json,search_text)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""",
                (
                    key,
                    citation["source_id"],
                    str(catalog_file).replace("\\", "/"),
                    citation["status"],
                    citation["summary"],
                    str(locator.get("printed_pages", "")),
                    str(locator.get("pdf_pages", "")),
                    json_text(locator),
                    json_text(local_text),
                    json_text(citation.get("use_for", [])),
                    json_text(citation.get("do_not_use_for", [])),
                    normalize_search_text("\n".join(search_parts)),
                ),
            )
            for ordinal, equation in enumerate(locator.get("equations", []), start=1):
                conn.execute(
                    "INSERT INTO citation_equations(citation_key,equation,ordinal) VALUES (?,?,?)",
                    (key, str(equation), ordinal),
                )
            ordinal = 0
            for statement in citation.get("extracted_claims", []):
                ordinal += 1
                claim_id = f"{key}.claim.{ordinal}"
                conn.execute(
                    """INSERT INTO claims(claim_id,citation_key,ordinal,claim_type,exactness,confidence,statement,assumptions_json,source_verified)
                       VALUES (?,?,?,?,?,?,?,?,?)""",
                    (claim_id, key, ordinal, "extracted_claim", "paraphrase", "catalogued", str(statement), "[]", 0),
                )
            for formula in citation.get("formulas", []):
                ordinal += 1
                claim_id = str(formula["id"])
                conn.execute(
                    """INSERT INTO claims(claim_id,citation_key,ordinal,claim_type,exactness,confidence,statement,formula_latex,formula_ascii,assumptions_json,conclusion,source_verified,notes)
                       VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                    (
                        claim_id,
                        key,
                        ordinal,
                        "formula",
                        formula.get("exactness", "normalized_formula"),
                        formula.get("confidence", "catalogued"),
                        formula.get("statement", ""),
                        formula.get("latex"),
                        formula.get("ascii"),
                        json_text(formula.get("assumptions", [])),
                        formula.get("conclusion"),
                        int(bool(formula.get("source_verified"))),
                        formula.get("notes"),
                    ),
                )
            for ordinal, target in enumerate(citation.get("lean_targets", []), start=1):
                conn.execute(
                    "INSERT INTO lean_targets(citation_key,lean_target,ordinal,relation,status) VALUES (?,?,?,?,?)",
                    (key, str(target), ordinal, "consumer", "targeted"),
                )
            for ordinal, question in enumerate(citation.get("open_questions", []), start=1):
                conn.execute(
                    "INSERT INTO open_questions(citation_key,ordinal,question,priority) VALUES (?,?,?,?)",
                    (key, ordinal, str(question), "normal"),
                )
            for link in citation.get("dictionary_links", []):
                conn.execute(
                    """INSERT INTO dictionary_links(link_id,citation_key,source_symbol,lean_symbol,relation,status,statement,blocker)
                       VALUES (?,?,?,?,?,?,?,?)""",
                    (
                        link["id"], key, link["source_symbol"], link["lean_symbol"],
                        link.get("relation", "corresponds_to"), link.get("status", "pending"),
                        link.get("statement"), link.get("blocker"),
                    ),
                )

        for record in records:
            for scan in record.data.get("scan_runs", []):
                conn.execute(
                    """INSERT INTO scan_runs(scan_id,source_id,artifact_name,page_start,page_end,method,scanned_at,agent,source_sha256,output_manifest,notes)
                       VALUES (?,?,?,?,?,?,?,?,?,?,?)""",
                    (
                        scan["scan_id"], scan["source_id"], scan.get("artifact_name"), scan.get("page_start"),
                        scan.get("page_end"), scan["method"], scan["scanned_at"], scan["agent"],
                        scan.get("source_sha256"), scan.get("output_manifest"), scan.get("notes"),
                    ),
                )
            for coverage in record.data.get("coverage", []):
                conn.execute(
                    """INSERT OR REPLACE INTO coverage(source_id,importance,catalog_status,artifact_status,formula_status,next_action,priority)
                       VALUES (?,?,?,?,?,?,?)""",
                    (
                        coverage["source_id"], coverage["importance"], coverage["catalog_status"],
                        coverage["artifact_status"], coverage["formula_status"], coverage["next_action"],
                        int(coverage["priority"]),
                    ),
                )
        conn.commit()
        conn.execute("PRAGMA optimize")
    finally:
        conn.close()
    temp.replace(output)
    temp.unlink(missing_ok=True)
    return output


def connect_existing(path: Path | None = None) -> sqlite3.Connection:
    path = path or db_path()
    if not path.exists():
        build_database(path)
    conn = sqlite3.connect(path)
    conn.row_factory = sqlite3.Row
    return conn


def print_source_acquisition(
    conn: sqlite3.Connection, source_id: str, indent: str = "  "
) -> None:
    source = conn.execute(
        "SELECT metadata_json FROM sources WHERE source_id=?", (source_id,)
    ).fetchone()
    if source is None:
        return
    artifacts = conn.execute(
        """SELECT artifact_name,relative_path,sha256,byte_size,media_type,exists_local
           FROM artifacts
           WHERE source_id=?
           ORDER BY exists_local,artifact_name""",
        (source_id,),
    ).fetchall()
    metadata = json.loads(source["metadata_json"])
    web_urls = metadata.get("web_urls", {})
    if not artifacts and not web_urls:
        return
    print(f"{indent}source acquisition:")
    print(f"{indent}  source root: {source_root()}")
    if web_urls:
        print(f"{indent}  web URLs:")
        for name, url in sorted(web_urls.items()):
            print(f"{indent}    - {name}: {url}")
    if artifacts:
        print(f"{indent}  local artifacts:")
        for artifact in artifacts:
            state = "present" if artifact["exists_local"] else "missing"
            print(
                f"{indent}    - {artifact['artifact_name']} [{state}] "
                f"{artifact['relative_path']}"
            )
            if artifact["media_type"]:
                print(f"{indent}      media: {artifact['media_type']}")
            if artifact["sha256"]:
                print(f"{indent}      sha256: {artifact['sha256']}")
            if artifact["byte_size"] is not None:
                print(f"{indent}      bytes: {artifact['byte_size']}")


def print_show(key: str, path: Path | None = None) -> None:
    with connect_existing(path) as conn:
        row = conn.execute(
            """SELECT c.*, s.short, s.title, s.doi
               FROM citations c JOIN sources s USING(source_id)
               WHERE citation_key=?""",
            (key,),
        ).fetchone()
        if row is None:
            raise SystemExit(f"unknown citation key: {key}")
        print(row["citation_key"])
        print(f"  source: {row['short']} — {row['title'] or '-'}")
        print(f"  DOI: {row['doi'] or '-'}")
        print(f"  status: {row['status']}")
        print(f"  pages: printed {row['printed_pages'] or '-'}; PDF {row['pdf_pages'] or '-'}")
        equations = [r[0] for r in conn.execute("SELECT equation FROM citation_equations WHERE citation_key=? ORDER BY ordinal", (key,))]
        print(f"  equations: {', '.join(equations) or '-'}")
        print(f"  summary: {row['summary']}")
        print_source_acquisition(conn, row["source_id"])
        local_text = json.loads(row["local_text_json"])
        if local_text:
            print("  local text:")
            for item in local_text:
                print(f"    - {item}")
        claims = conn.execute(
            "SELECT * FROM claims WHERE citation_key=? ORDER BY ordinal", (key,)
        ).fetchall()
        if claims:
            print("  claims/formulas:")
            for claim in claims:
                marker = "✓" if claim["source_verified"] else "·"
                print(f"    {marker} [{claim['exactness']}/{claim['confidence']}] {claim['statement']}")
                if claim["formula_ascii"]:
                    print(f"      {claim['formula_ascii']}")
        targets = [r[0] for r in conn.execute("SELECT lean_target FROM lean_targets WHERE citation_key=? ORDER BY ordinal", (key,))]
        if targets:
            print("  Lean targets:")
            for target in targets:
                print(f"    - {target}")
        links = conn.execute(
            """SELECT source_symbol,lean_symbol,relation,status,statement,blocker
               FROM dictionary_links
               WHERE citation_key=?
               ORDER BY link_id""",
            (key,),
        ).fetchall()
        if links:
            print("  dictionary links:")
            for link in links:
                print(
                    f"    - {link['source_symbol']} -> {link['lean_symbol']} "
                    f"[{link['relation']}/{link['status']}]"
                )
                if link["statement"]:
                    print(f"      statement: {link['statement']}")
                if link["blocker"]:
                    print(f"      blocker: {link['blocker']}")
        questions = [r[0] for r in conn.execute("SELECT question FROM open_questions WHERE citation_key=? ORDER BY ordinal", (key,))]
        if questions:
            print("  open questions:")
            for question in questions:
                print(f"    - {question}")


def print_search(term: str, path: Path | None = None) -> None:
    needle = f"%{normalize_search_text(term)}%"
    with connect_existing(path) as conn:
        rows = conn.execute(
            """SELECT citation_key,status,summary,printed_pages,pdf_pages
               FROM citations
               WHERE search_text LIKE ? OR lower(citation_key) LIKE ?
               ORDER BY citation_key""",
            (needle, needle),
        ).fetchall()
        if not rows:
            print("no matches")
            return
        for row in rows:
            print(f"{row['citation_key']} [{row['status']}] pp. {row['printed_pages']}/{row['pdf_pages']}")
            print(f"  {row['summary']}")


def print_lean(term: str, path: Path | None = None) -> None:
    needle = f"%{term.lower()}%"
    with connect_existing(path) as conn:
        rows = conn.execute(
            """SELECT l.lean_target,c.citation_key,c.status,c.summary
               FROM lean_targets l JOIN citations c USING(citation_key)
               WHERE lower(l.lean_target) LIKE ?
               ORDER BY l.lean_target,c.citation_key""",
            (needle,),
        ).fetchall()
        if not rows:
            print("no Lean target matches")
            return
        for row in rows:
            print(f"{row['lean_target']} <- {row['citation_key']} [{row['status']}]")
            print(f"  {row['summary']}")


def print_blockers(path: Path | None = None) -> None:
    with connect_existing(path) as conn:
        placeholders = ",".join("?" for _ in BLOCKING_STATUSES)
        rows = conn.execute(
            f"""SELECT citation_key,status,summary,printed_pages,pdf_pages
                FROM citations WHERE status IN ({placeholders})
                ORDER BY CASE status
                  WHEN 'ocr_corrupted' THEN 0
                  WHEN 'source_pending' THEN 1
                  WHEN 'located' THEN 2
                  ELSE 3 END, citation_key""",
            tuple(BLOCKING_STATUSES),
        ).fetchall()
        for row in rows:
            print(f"{row['citation_key']} [{row['status']}] pp. {row['printed_pages']}/{row['pdf_pages']}")
            print(f"  {row['summary']}")
            question = conn.execute(
                "SELECT question FROM open_questions WHERE citation_key=? ORDER BY ordinal LIMIT 1",
                (row["citation_key"],),
            ).fetchone()
            if question:
                print(f"  next: {question[0]}")


def print_frontier(
    term: str | None = None,
    status: str | None = None,
    limit: int = 40,
    path: Path | None = None,
) -> None:
    params: list[Any] = []
    filters = ["EXISTS (SELECT 1 FROM open_questions q WHERE q.citation_key=c.citation_key)"]
    if status:
        filters.append("c.status=?")
        params.append(status)
    if term:
        needle = f"%{normalize_search_text(term)}%"
        filters.append("(c.search_text LIKE ? OR lower(c.citation_key) LIKE ?)")
        params.extend([needle, f"%{term.lower()}%"])
    where = " AND ".join(filters)
    params.append(limit)
    with connect_existing(path) as conn:
        rows = conn.execute(
            f"""SELECT c.citation_key,c.status,c.summary,c.printed_pages,c.pdf_pages,
                       c.source_id,c.local_text_json,
                       count(DISTINCT q.ordinal) AS question_count,
                       count(DISTINCT l.lean_target) AS target_count
                FROM citations c
                LEFT JOIN open_questions q USING(citation_key)
                LEFT JOIN lean_targets l USING(citation_key)
                WHERE {where}
                GROUP BY c.citation_key
                ORDER BY CASE c.status
                  WHEN 'ocr_corrupted' THEN 0
                  WHEN 'source_pending' THEN 1
                  WHEN 'lean_linked' THEN 2
                  WHEN 'located' THEN 3
                  WHEN 'visual_confirmed' THEN 4
                  ELSE 5 END,
                  target_count DESC, question_count DESC, c.citation_key
                LIMIT ?""",
            tuple(params),
        ).fetchall()
        if not rows:
            print("no frontier entries")
            return
        for row in rows:
            print(
                f"{row['citation_key']} [{row['status']}] "
                f"targets={row['target_count']} questions={row['question_count']} "
                f"pp. {row['printed_pages']}/{row['pdf_pages']}"
            )
            print(f"  {row['summary']}")
            question = conn.execute(
                "SELECT question FROM open_questions WHERE citation_key=? ORDER BY ordinal LIMIT 1",
                (row["citation_key"],),
            ).fetchone()
            if question:
                print(f"  next: {question[0]}")
            local_text = json.loads(row["local_text_json"])
            if local_text:
                print(f"  local: {local_text[0]}")
            artifacts = conn.execute(
                """SELECT count(*) AS n,
                          sum(CASE WHEN exists_local THEN 1 ELSE 0 END) AS present
                   FROM artifacts
                   WHERE source_id=?""",
                (row["source_id"],),
            ).fetchone()
            metadata = conn.execute(
                "SELECT metadata_json FROM sources WHERE source_id=?", (row["source_id"],)
            ).fetchone()
            web_count = 0
            if metadata is not None:
                web_count = len(json.loads(metadata["metadata_json"]).get("web_urls", {}))
            if artifacts and (artifacts["n"] or web_count):
                present = artifacts["present"] or 0
                print(
                    f"  acquisition: artifacts {present}/{artifacts['n']} present; "
                    f"urls={web_count}"
                )


def print_coverage(path: Path | None = None) -> None:
    with connect_existing(path) as conn:
        rows = conn.execute(
            """SELECT c.*,s.short FROM coverage c JOIN sources s USING(source_id)
               ORDER BY priority DESC,source_id"""
        ).fetchall()
        for row in rows:
            print(f"P{row['priority']:02d} {row['source_id']} — {row['short']} [{row['catalog_status']}; {row['formula_status']}; {row['artifact_status']}]")
            print(f"  {row['next_action']}")


def print_artifacts(source_id: str | None = None, path: Path | None = None) -> None:
    with connect_existing(path) as conn:
        params: tuple[str, ...] = ()
        where = ""
        if source_id:
            where = "WHERE s.source_id=?"
            params = (source_id,)
        sources = conn.execute(
            f"""SELECT s.source_id,s.short,s.metadata_json
                FROM sources s
                {where}
                ORDER BY s.source_id""",
            params,
        ).fetchall()
        if not sources:
            raise SystemExit(f"unknown source_id: {source_id}")
        print(f"source root: {source_root()}")
        for source in sources:
            artifacts = conn.execute(
                """SELECT artifact_name,relative_path,sha256,byte_size,media_type,exists_local
                   FROM artifacts
                   WHERE source_id=?
                   ORDER BY exists_local,artifact_name""",
                (source["source_id"],),
            ).fetchall()
            metadata = json.loads(source["metadata_json"])
            web_urls = metadata.get("web_urls", {})
            if not artifacts and not web_urls:
                continue
            print(f"{source['source_id']} - {source['short']}")
            if web_urls:
                print("  web URLs:")
                for name, url in sorted(web_urls.items()):
                    print(f"    - {name}: {url}")
            if artifacts:
                print("  local artifacts:")
                for artifact in artifacts:
                    state = "present" if artifact["exists_local"] else "missing"
                    print(
                        f"    - {artifact['artifact_name']} [{state}] "
                        f"{artifact['relative_path']}"
                    )
                    full = source_root() / artifact["relative_path"]
                    print(f"      path: {full}")
                    if artifact["media_type"]:
                        print(f"      media: {artifact['media_type']}")
                    if artifact["sha256"]:
                        print(f"      sha256: {artifact['sha256']}")
                    if artifact["byte_size"] is not None:
                        print(f"      bytes: {artifact['byte_size']}")


def verify(root: Path | None = None, check_local: bool = False) -> int:
    root = root or repo_root()
    records = load_catalogs(root)
    errors = validate_catalogs(records, root)
    if check_local:
        sources = merge_sources(records)
        local_root = source_root()
        for source_id, source in sources.items():
            for name, relpath in source.get("local_artifacts", {}).items():
                path = local_root / str(relpath)
                if not path.exists():
                    errors.append(f"missing local artifact: {source_id}.{name}: {path}")
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(f"OK: {len(records)} catalog file(s), no structural errors")
    if check_local:
        print(f"OK: local artifacts checked under {source_root()}")
    return 0


def manifest_for_local_artifacts(records: list[CatalogRecord]) -> dict[str, Any]:
    sources = merge_sources(records)
    entries: list[dict[str, Any]] = []
    for source_id in sorted(sources):
        source = sources[source_id]
        for name, relpath in sorted(source.get("local_artifacts", {}).items()):
            path = source_root() / str(relpath)
            entry: dict[str, Any] = {
                "source_id": source_id,
                "artifact_name": name,
                "relative_path": str(relpath).replace("\\", "/"),
                "exists": path.exists(),
            }
            if path.exists() and path.is_file():
                entry["sha256"] = sha256_file(path)
                entry["byte_size"] = path.stat().st_size
                entry["media_type"] = artifact_media_type(str(relpath))
            entries.append(entry)
    return {
        "schema_version": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source_root": str(source_root()),
        "artifacts": entries,
    }


def zip_add_file(zf: zipfile.ZipFile, source: Path, arcname: str) -> None:
    info = zipfile.ZipInfo(arcname.replace("\\", "/"), FIXED_ZIP_TIME)
    info.compress_type = zipfile.ZIP_DEFLATED
    info.external_attr = 0o644 << 16
    zf.writestr(info, source.read_bytes())


def build_packet(output: Path, include_raw: bool, root: Path | None = None) -> Path:
    root = root or repo_root()
    database = build_database(root=root)
    records = load_catalogs(root)
    manifest = manifest_for_local_artifacts(records)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.unlink(missing_ok=True)

    public_files: list[Path] = []
    for rel in ("docs/source-db", "docs/source-citations", "scripts", "tests"):
        base = root / rel
        if base.exists():
            public_files.extend(path for path in base.rglob("*") if path.is_file())
    for filename in (
        "AGENT_BUILDER_PROMPT.md",
        "SOURCE_DB_INSTALL.md",
        "INITIAL_AUDIT.md",
        "install_into_repo.py",
        "source-packets/README.md",
        "source-packets/private/.gitkeep",
        ".gitignore",
    ):
        path = root / filename
        if path.exists():
            public_files.append(path)

    with tempfile.TemporaryDirectory() as tmpdir:
        manifest_path = Path(tmpdir) / "source-artifact-manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        with zipfile.ZipFile(output, "w") as zf:
            for path in sorted(set(public_files)):
                if path.name.endswith(("-wal", "-shm", ".tmp")):
                    continue
                zip_add_file(zf, path, str(path.relative_to(root)))
            zip_add_file(zf, manifest_path, "source-packets/manifests/source-artifact-manifest.json")
            if include_raw:
                for entry in manifest["artifacts"]:
                    if not entry.get("exists"):
                        continue
                    source = source_root() / entry["relative_path"]
                    arcname = f"source-packets/private/{entry['source_id']}/{entry['relative_path']}"
                    zip_add_file(zf, source, arcname)
    print(f"packet: {output}")
    print(f"sha256: {sha256_file(output)}")
    if include_raw:
        included = sum(1 for item in manifest["artifacts"] if item.get("exists"))
        print(f"raw artifacts included: {included}")
    else:
        print("raw artifacts included: 0 (metadata-only packet)")
    return output


def command_stats(path: Path | None = None) -> None:
    with connect_existing(path) as conn:
        for table in ("sources", "citations", "claims", "lean_targets", "open_questions", "artifacts", "coverage"):
            count = conn.execute(f"SELECT count(*) FROM {table}").fetchone()[0]
            print(f"{table}: {count}")
        print("statuses:")
        for row in conn.execute("SELECT status,count(*) n FROM citations GROUP BY status ORDER BY status"):
            print(f"  {row['status']}: {row['n']}")


def source_metadata_text_paths(root: Path | None = None) -> list[Path]:
    """Return source metadata files whose commit anchors guide source agents."""
    root = root or repo_root()
    bases = [root / "docs" / "source-db", root / "docs" / "source-citations"]
    suffixes = {".json", ".md", ".csv"}
    paths: list[Path] = []
    for base in bases:
        if base.exists():
            paths.extend(
                path for path in base.rglob("*")
                if path.is_file() and path.suffix.lower() in suffixes
            )
    return sorted(paths)


def iter_head_references(root: Path | None = None) -> Iterator[tuple[Path, int, str, str]]:
    root = root or repo_root()
    for path in source_metadata_text_paths(root):
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        for lineno, line in enumerate(text.splitlines(), start=1):
            for match in GIT_COMMIT_REF.finditer(line):
                yield path.relative_to(root), lineno, match.group(1).lower(), line.strip()


def classify_commit_ref(root: Path, commit: str, head: str) -> str:
    resolved = run_git(root, "rev-parse", "--verify", f"{commit}^{{commit}}")
    if resolved.returncode != 0:
        return "missing"
    resolved_hash = resolved.stdout.strip()
    if resolved_hash == head:
        return "current"
    ancestor = run_git(root, "merge-base", "--is-ancestor", resolved_hash, head)
    if ancestor.returncode == 0:
        return "ancestor"
    return "not-ancestor"


def print_head_refs(root: Path | None = None) -> None:
    root = root or repo_root()
    head_proc = run_git(root, "rev-parse", "HEAD")
    if head_proc.returncode != 0:
        raise SystemExit(head_proc.stderr.strip() or "cannot determine git HEAD")
    head = head_proc.stdout.strip()
    print(f"current HEAD: {head[:7]} {head}")

    refs: dict[str, list[tuple[Path, int, str]]] = {}
    for path, lineno, commit, line in iter_head_references(root):
        refs.setdefault(commit, []).append((path, lineno, line))
    if not refs:
        print("no source metadata HEAD/git-commit references found")
        return

    for commit in sorted(refs):
        locations = refs[commit]
        print(f"{commit} [{classify_commit_ref(root, commit, head)}] {len(locations)} reference(s)")
        for path, lineno, line in locations[:6]:
            print(f"  {path.as_posix()}:{lineno}: {line}")
        if len(locations) > 6:
            print(f"  ... {len(locations) - 6} more")


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    sub.add_parser("build", help="build the generated SQLite index")
    verify_parser = sub.add_parser("verify", help="validate all JSON catalogs")
    verify_parser.add_argument("--check-local", action="store_true", help="also require every registered local artifact")
    show = sub.add_parser("show", help="show one citation")
    show.add_argument("key")
    search = sub.add_parser("search", help="full-text-like search over citations and formulas")
    search.add_argument("term")
    lean = sub.add_parser("lean", help="find citations linked to a Lean declaration")
    lean.add_argument("term")
    sub.add_parser("blockers", help="list non-theorem-feedable entries")
    frontier = sub.add_parser("frontier", help="list open source/Lean frontier entries")
    frontier.add_argument("--term", help="optional search filter")
    frontier.add_argument("--status", choices=sorted(VALID_STATUSES), help="optional status filter")
    frontier.add_argument("--limit", type=int, default=40, help="maximum entries to print")
    sub.add_parser("coverage", help="show source-spine coverage and priorities")
    artifacts = sub.add_parser("artifacts", help="show required local artifacts and acquisition URLs")
    artifacts.add_argument("source_id", nargs="?", help="optional source id to filter")
    sub.add_parser("stats", help="show database statistics")
    sub.add_parser("head-refs", help="list git HEAD/commit anchors in source metadata")
    packet = sub.add_parser("packet", help="create a reproducible source packet ZIP")
    packet.add_argument("--output", type=Path, default=repo_root() / "source-packets" / "out" / "source-packet.zip")
    packet.add_argument("--include-raw", action="store_true", help="include user-local PDFs/OCR/renders from YM_SOURCE_ROOT")
    return p


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if args.command == "build":
        path = build_database()
        print(path)
        print(sha256_file(path))
        return 0
    if args.command == "verify":
        return verify(check_local=args.check_local)
    if args.command == "show":
        print_show(args.key)
        return 0
    if args.command == "search":
        print_search(args.term)
        return 0
    if args.command == "lean":
        print_lean(args.term)
        return 0
    if args.command == "blockers":
        print_blockers()
        return 0
    if args.command == "frontier":
        print_frontier(term=args.term, status=args.status, limit=args.limit)
        return 0
    if args.command == "coverage":
        print_coverage()
        return 0
    if args.command == "artifacts":
        print_artifacts(args.source_id)
        return 0
    if args.command == "stats":
        command_stats()
        return 0
    if args.command == "head-refs":
        print_head_refs()
        return 0
    if args.command == "packet":
        build_packet(args.output, args.include_raw)
        return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
