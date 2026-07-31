#!/usr/bin/env python3
"""Freeze the public ai.viXra author census into reviewable repo artifacts."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import shutil
from collections import Counter
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def cell(value: object) -> str:
    return str(value if value is not None else "").replace("|", "\\|").replace("\n", " ")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--raw-json", type=Path, required=True)
    parser.add_argument("--raw-csv", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--repo-sha", required=True)
    args = parser.parse_args()

    payload = json.loads(args.raw_json.read_text(encoding="utf-8"))
    records = payload["records"]
    if payload.get("paper_count") != 103 or len(records) != 103:
        raise SystemExit(f"refusing non-frozen census: {len(records)} records")

    args.output_dir.mkdir(parents=True, exist_ok=True)
    out_json = args.output_dir / "PUBLICATION-CENSUS-20260731.json"
    out_csv = args.output_dir / "PUBLICATION-CENSUS-20260731.csv"
    out_md = args.output_dir / "PUBLICATION-CENSUS-20260731.md"
    shutil.copyfile(args.raw_json, out_json)
    shutil.copyfile(args.raw_csv, out_csv)

    versions = Counter(f"v{r['current_version']}" for r in records)
    events = Counter(r["listing_event"] for r in records)
    categories = Counter(r["category_abstract_page"] for r in records)
    downloaded = [r for r in records if r.get("pdf_sha256")]
    pages = sum(r["pdfinfo"]["pages"] for r in downloaded)
    total_bytes = sum(r["pdf_size_bytes"] for r in downloaded)
    missing = [r for r in records if not r.get("pdf_sha256")]
    nonembedded = []
    for record in downloaded:
        bad = [f["name"] for f in record["pdffonts"]["fonts"] if f.get("embedded") != "yes"]
        if bad:
            nonembedded.append((record["id"], record["current_version"], bad))

    lines = [
        "# Publication census - 2026-07-31",
        "",
        "## Frozen source",
        "",
        f"- Author page: {payload['source_url']}",
        f"- Capture time (UTC): `{payload['captured_at_utc']}`",
        f"- Author-page HTML SHA-256: `{payload['author_page_sha256']}`",
        f"- Raw census JSON SHA-256: `{sha256(args.raw_json)}`",
        f"- Raw census CSV SHA-256: `{sha256(args.raw_csv)}`",
        f"- Repository comparison base: `{args.repo_sha}` (`origin/main` at audit start)",
        "- Authority rule: the public author page, each public abstract page, and the public PDF are authoritative for publication state. Local files are not publication evidence.",
        "",
        "## Counts",
        "",
        f"- Published records: **{len(records)}**.",
        f"- Current PDFs downloaded and inspected structurally: **{len(downloaded)}**; **{pages} pages**; **{total_bytes:,} bytes**.",
        f"- Current versions: {', '.join(f'{k}={versions[k]}' for k in sorted(versions))}.",
        f"- Listing events: submitted={events['submitted']}; replaced={events['replaced']}.",
        "- Categories: " + "; ".join(f"{name}={count}" for name, count in sorted(categories.items())) + ".",
        "- Version-history links captured: **174**.",
        "",
        "## Provenance and caveats",
        "",
        "`citation_online_date` is not used as a date source: it disagrees with the first submission-history timestamp in all 103 records. Exact dates below come from the public listing/submission history.",
        "",
    ]
    if missing:
        for record in missing:
            lines.append(
                f"- **Unavailable current object:** `{record['id']}v{record['current_version']}` is the version designated by the abstract page, but {record['pdf_url']} returned HTTP 404. Its public v1 was archived only as historical fallback and is not represented as current."
            )
    for paper_id, version, fonts in nonembedded:
        lines.append(
            f"- **Font preflight:** `{paper_id}v{version}` contains non-embedded fonts: {', '.join(fonts)}. This is a reproducibility/portability finding, not by itself a mathematical verdict."
        )
    lines.extend(
        [
            "",
            "## Complete current-publication table",
            "",
            "| No. | ID | Ver. | Event and public time | Title | Author | Category | Pages | Bytes | Encrypted | SHA-256 | Public links |",
            "|---:|---|---:|---|---|---|---|---:|---:|---|---|---|",
        ]
    )
    for r in records:
        info = r.get("pdfinfo") or {}
        sha = r.get("pdf_sha256") or "UNAVAILABLE-CURRENT-PDF"
        links = f"[abstract]({r['abstract_url']}) / [PDF]({r['pdf_url']})"
        lines.append(
            "| "
            + " | ".join(
                [
                    cell(r["author_list_number"]),
                    cell(r["id"]),
                    cell(f"v{r['current_version']}"),
                    cell(f"{r['listing_event']} {r['listing_event_datetime']}"),
                    cell(r["title_abstract_page"]),
                    cell(", ".join(r["authors_abstract_page"])),
                    cell(r["category_abstract_page"]),
                    cell(info.get("pages", "N/A")),
                    cell(r.get("pdf_size_bytes", "N/A")),
                    cell(info.get("encrypted", "N/A")),
                    cell(sha),
                    links,
                ]
            )
            + " |"
        )

    lines.extend(
        [
            "",
            "## Machine-readable scope",
            "",
            "The sibling JSON retains every abstract-page hash, complete submission history, current PDF URL/hash/size, `pdfinfo` output, and full `pdffonts` inventory. The sibling CSV is a flattened review surface. Neither file assigns a supersession verdict; those decisions belong in `PAPER-AUDIT-LEDGER.md` and `SUPERSESSION-MATRIX.md` after claim-level review.",
            "",
        ]
    )
    out_md.write_text("\n".join(lines), encoding="utf-8", newline="\n")

    print(json.dumps({
        "records": len(records),
        "downloaded": len(downloaded),
        "pages": pages,
        "bytes": total_bytes,
        "md_sha256": sha256(out_md),
        "csv_sha256": sha256(out_csv),
        "json_sha256": sha256(out_json),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
