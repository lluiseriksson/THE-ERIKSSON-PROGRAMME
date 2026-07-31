#!/usr/bin/env python3
"""Validate the canonical publication crosswalk and active public front doors."""

from __future__ import annotations

import datetime as dt
import json
import re
import sys
from pathlib import Path, PurePosixPath
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DATA_PATH = ROOT / "docs" / "publications.json"
REGISTER_PATH = ROOT / "docs" / "PUBLICATIONS.md"
PUBLIC_ID = re.compile(r"^26\d{2}\.\d{4}$")
PLACEHOLDER = re.compile(
    r"ai\.viXra(?:\.org)?:\s*(?:X{4}\.X{4}|TBD|PENDING)|"
    r"add the ID when published",
    re.IGNORECASE,
)
STATUSES = {"published", "published-unmirrored", "repository-only"}
ACTIVE_FRONT_DOORS = (
    "README.md",
    "CURRENT-STATE.md",
    "README-FOR-NEXT-MODEL.md",
    "AGENT-ONBOARDING.md",
    "CLAUDE.md",
    "docs/PUBLICATIONS.md",
    "docs/publications.json",
    "docs/dashboard/data.json",
    "docs/dashboard/index.html",
)


def _repo_file(value: Any, field: str, errors: list[str]) -> Path | None:
    if not isinstance(value, str) or not value:
        errors.append(f"{field}: expected a non-empty repository-relative path")
        return None
    relative = PurePosixPath(value)
    if relative.is_absolute() or ".." in relative.parts:
        errors.append(f"{field}: path must remain inside the repository")
        return None
    path = ROOT.joinpath(*relative.parts)
    if not path.is_file():
        errors.append(f"{field}: repository artifact does not exist: {value}")
        return None
    return path


def _load_data(errors: list[str]) -> dict[str, Any]:
    try:
        data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"docs/publications.json: {exc}")
        return {}
    if not isinstance(data, dict):
        errors.append("docs/publications.json: expected a JSON object")
        return {}
    return data


def validate_publications() -> list[str]:
    errors: list[str] = []
    data = _load_data(errors)
    if data.get("schema_version") != 1:
        errors.append("docs/publications.json: schema_version must be 1")
    try:
        dt.date.fromisoformat(str(data.get("verified_on", "")))
    except ValueError:
        errors.append("docs/publications.json: verified_on must be an ISO date")
    if data.get("author_index") != "https://www.ai.vixra.org/author/lluis_eriksson":
        errors.append("docs/publications.json: unexpected author_index")

    entries = data.get("entries")
    if not isinstance(entries, list):
        errors.append("docs/publications.json: entries must be an array")
        entries = []

    seen_ids: set[str] = set()
    seen_artifacts: set[str] = set()
    public_ids_in_order: list[str] = []
    published: dict[str, dict[str, Any]] = {}
    register = (
        REGISTER_PATH.read_text(encoding="utf-8")
        if REGISTER_PATH.is_file()
        else ""
    )
    if not register:
        errors.append("docs/PUBLICATIONS.md: missing or empty")

    for index, raw in enumerate(entries):
        label = f"entries[{index}]"
        if not isinstance(raw, dict):
            errors.append(f"{label}: expected an object")
            continue
        status = raw.get("status")
        paper_id = raw.get("id")
        title = raw.get("title")
        artifact = raw.get("artifact")
        if status not in STATUSES:
            errors.append(f"{label}: invalid status {status!r}")
        if not isinstance(title, str) or not title.strip():
            errors.append(f"{label}: title must be non-empty")

        if status in {"published", "published-unmirrored"}:
            if not isinstance(paper_id, str) or not PUBLIC_ID.fullmatch(paper_id):
                errors.append(f"{label}: public paper requires a valid ai.viXra id")
            else:
                if paper_id in seen_ids:
                    errors.append(f"{label}: duplicate public id {paper_id}")
                seen_ids.add(paper_id)
                public_ids_in_order.append(paper_id)
                published[paper_id] = raw
                if paper_id not in register:
                    errors.append(f"docs/PUBLICATIONS.md: missing public id {paper_id}")
        elif status == "repository-only" and paper_id is not None:
            errors.append(f"{label}: repository-only paper must have id null")

        if status in {"published", "repository-only"}:
            if _repo_file(artifact, f"{label}.artifact", errors) is not None:
                if artifact in seen_artifacts:
                    errors.append(f"{label}: duplicate artifact {artifact}")
                seen_artifacts.add(artifact)
                if artifact not in register:
                    errors.append(
                        f"docs/PUBLICATIONS.md: missing artifact path {artifact}"
                    )
        elif status == "published-unmirrored" and artifact is not None:
            errors.append(f"{label}: published-unmirrored artifact must be null")

    if public_ids_in_order != sorted(public_ids_in_order, reverse=True):
        errors.append(
            "docs/publications.json: public entries must be sorted by descending id"
        )

    area_law = published.get("2607.0005")
    if not area_law or area_law.get("artifact") != "paper/area-law/paper.pdf":
        errors.append(
            "docs/publications.json: area-law must map 2607.0005 to "
            "paper/area-law/paper.pdf"
        )

    exceptions = data.get("exceptions")
    if not isinstance(exceptions, list):
        errors.append("docs/publications.json: exceptions must be an array")
    else:
        for index, raw in enumerate(exceptions):
            label = f"exceptions[{index}]"
            if not isinstance(raw, dict):
                errors.append(f"{label}: expected an object")
                continue
            exception_id = raw.get("id")
            canonical_id = raw.get("canonical_id")
            if not isinstance(exception_id, str) or not PUBLIC_ID.fullmatch(exception_id):
                errors.append(f"{label}: invalid exception id")
            if canonical_id not in published:
                errors.append(f"{label}: canonical_id is not a published entry")

    for relative in ACTIVE_FRONT_DOORS:
        path = ROOT / relative
        if not path.is_file():
            errors.append(f"{relative}: file does not exist")
            continue
        text = path.read_text(encoding="utf-8")
        if PLACEHOLDER.search(text):
            errors.append(f"{relative}: contains a publication placeholder")

    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    if "https://ai.vixra.org/abs/2607.0005" not in readme:
        errors.append("README.md: area-law public record 2607.0005 is missing")
    dashboard = json.loads(
        (ROOT / "docs" / "dashboard" / "data.json").read_text(encoding="utf-8")
    )
    meta = dashboard.get("meta", {}) if isinstance(dashboard, dict) else {}
    if not str(meta.get("publications", "")).endswith("docs/PUBLICATIONS.md"):
        errors.append("docs/dashboard/data.json: publication register link is missing")
    if meta.get("author_index") != data.get("author_index"):
        errors.append("docs/dashboard/data.json: author index disagrees with crosswalk")

    return errors


def main() -> int:
    errors = validate_publications()
    if errors:
        print(f"publication validation: {len(errors)} problem(s)")
        for error in errors:
            print(f"  - {error}")
        return 1

    data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    public = [
        entry
        for entry in data["entries"]
        if entry["status"] in {"published", "published-unmirrored"}
    ]
    mirrored = [entry for entry in public if entry["artifact"]]
    repository_only = [
        entry for entry in data["entries"] if entry["status"] == "repository-only"
    ]
    print(
        "publication validation OK - "
        f"{len(public)} public works, {len(mirrored)} mirrored PDFs, "
        f"{len(repository_only)} repository-only manuscripts"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
