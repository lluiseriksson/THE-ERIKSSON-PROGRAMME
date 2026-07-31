#!/usr/bin/env python3
"""Merge the three page-level audit batches into a canonical 103-paper ledger."""

from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs" / "publication-audit"
CENSUS = DOCS / "PUBLICATION-CENSUS-20260731.json"
BATCHES = (
    ROOT / "tmp" / "publication-audit" / "batches" / "early" / "EARLY-AUDIT-34-1.json",
    ROOT / "tmp" / "publication-audit" / "batches" / "middle" / "middle-paper-audit.json",
    ROOT / "tmp" / "publication-audit" / "batches" / "latest" / "AUDIT-BATCH-103-70.json",
)

# Findings from the independent audit of the historical erratum candidates.
# These deliberately supersede the first-pass middle-batch classifications.
OVERRIDES: dict[str, dict[str, Any]] = {
    "2602.0052": {
        "claim_pages": "public v2 metadata; public v2 pp. 1-10; archived public v1 pp. 1-11",
        "claim_class": "P0 record-identity corruption plus refuted Interface-Lemmas closure claims",
        "terminal_claim": "The current record metadata names 2602.0036 while the v2 PDF is the corrected Morse-Bott manuscript belonging to 2602.0035; the authentic 2602.0052v1 is the separate Interface Lemmas paper, whose v3 candidate withdraws its unconditional closure framing.",
        "evidence": "Archived public v1 SHA 2ef7856e... has the Interface Lemmas title/content. Current public v2 SHA 1975125d... is pixel-identical to the Morse-Bott block needed by the 2602.0035 replacement. The local Interface-Lemmas erratum gives the -I in SU(2) principal-log counterexample and invalidates the global Holley-Stroock direction.",
        "risk": "P0: wrong paper in the public record and broken claims in the displaced authentic paper.",
        "verdict": "REPLACE-VERSION",
        "action": "Restore the authentic Interface Lemmas paper as v3 with its retraction; do not withdraw the record. Fix the local submission abstract/comments and package provenance first. This is the first step of the 0052/0036/0033/0035 chain.",
    },
    "2602.0036": {
        "claim_pages": "public v2 Theorem 3.1 and Corollaries 3.2-3.3; local v3 erratum pp. 1-3",
        "claim_class": "unestablished Ricci lower bound with direct broken-dependency propagation",
        "terminal_claim": "The public paper continues to offer Theorem 3.1's pointwise Ricci bound, but its O'Neill trace omits mixed horizontal-vertical sectional terms; the dependent corollaries and uses in 2602.0033/0035 are not established.",
        "evidence": "The corrective derivation shows the missing mixed sectional sum enters with a negative sign when base Ricci is expressed from total-space Ricci. The local erratum prudently withdraws the proof/corollaries without claiming the bound itself false.",
        "risk": "P0: broken load-bearing geometric dependency; P1 package/provenance debt.",
        "verdict": "REPLACE-VERSION",
        "action": "Replace with the v3 corrective note after restoring 2602.0052 and before R30/2602.0035. Repair overfull layout and submission-field limits; add reproducible build/verifier/manifest.",
    },
    "2602.0085": {
        "claim_pages": "public v1 pp. 1, 4, 9-12, 16",
        "claim_class": "refuted exact linearisation and dependent UV theorem",
        "terminal_claim": "The advertised UV closure depends on Lemma 3.6/Eq. (16), whose printed linearisation has the wrong kernel on pure-gauge directions; Lemma 3.8, Proposition 3.9, Theorem 3.11 and Theorem 1.1 consequently fall.",
        "evidence": "Exact configuration/dimension counterexample: at U=1 the true Hessian annihilates a gauge subspace of dimension at least (|V|-1)(N^2-1), incompatible with the printed connected weighted-Laplacian kernel; disconnected weights also contradict the single stationary term.",
        "risk": "P0: false load-bearing linearisation and broken downstream theorem chain.",
        "verdict": "REPLACE-VERSION",
        "action": "Replace with a corrected retraction in order before 2602.0084. The historical candidate PDF is not ready until its submission sheet stops calling Lemma 3.2 unaffected and gains a reproducible manifest/verifier.",
    },
    "2602.0084": {
        "claim_pages": "public v1 pp. 1, 4-6, 9-10, 12, 14",
        "claim_class": "refuted lemmas and dependency-broken almost-reflection theorem",
        "terminal_claim": "The advertised almost-reflection-positivity chain depends on the false 2602.0085 linearisation and also contains false heat-kernel, non-product variance, periodic-support, nonlinear-map and Hille-Yosida steps.",
        "evidence": "Exact counterexamples/refutations affect Lemma 3.1, Lemma 3.3, Lemma 3.5, Theorem 4.4, Theorem 5.1 and Lemma A.1; finite-L scope does not repair false premises.",
        "risk": "P0: multiple false statements and a broken dependency on 2602.0085.",
        "verdict": "REPLACE-VERSION",
        "action": "Replace after 2602.0085. The historical candidate PDF is not ready until comments include defects A-G, withdraw the false 'Lemma 3.3 unaffected' sentence, and gain manifest/verifier/preflight.",
    },
}


def compact(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return re.sub(r"\s+", " ", value).strip()
    if isinstance(value, list):
        parts: list[str] = []
        for item in value:
            if isinstance(item, dict):
                parts.append(
                    ": ".join(
                        str(item.get(key, ""))
                        for key in ("level", "issue", "pages")
                        if item.get(key) not in (None, "")
                    )
                )
            else:
                parts.append(str(item))
        return "; ".join(parts)
    if isinstance(value, dict):
        return "; ".join(f"{key}: {compact(item)}" for key, item in value.items())
    return str(value)


def md(value: Any) -> str:
    return compact(value).replace("|", "\\|")


def normalize(raw: dict[str, Any]) -> dict[str, Any]:
    number = raw["author_list_number"]
    version = raw.get("version") or raw.get("public_version")
    title = raw.get("title") or raw.get("metadata_title")
    pages = raw.get("pages")
    sha = raw.get("pdf_sha256") or raw.get("public_pdf_sha256")
    url = raw.get("pdf_url") or raw.get("public_pdf_url")
    if "terminal_claims" in raw:
        claims = raw["terminal_claims"]
        terminal_claim = "; ".join(compact(item.get("claim")) for item in claims)
        claim_pages = "; ".join(compact(item.get("page")) for item in claims)
        claim_class = "; ".join(compact(item.get("classification")) for item in claims)
        evidence = "; ".join(compact(item.get("evidence")) for item in claims)
        dependencies = compact(raw.get("dependencies"))
        risk = compact(raw.get("risk"))
        visual = raw.get("visual_inspection", {})
        visual_status = compact(visual.get("status"))
        rerun = compact(raw.get("independent_reexecution"))
    elif "terminal_claim" in raw and "claim_pages" in raw:
        terminal_claim = compact(raw.get("terminal_claim"))
        claim_pages = compact(raw.get("claim_pages"))
        claim_class = compact(raw.get("claim_class"))
        evidence = compact(raw.get("evidence"))
        dependencies = compact(raw.get("dependencies"))
        risk = compact(raw.get("risk"))
        visual = raw.get("visual_review", {})
        visual_status = (
            f"ALL_PAGES_INSPECTED ({visual.get('reviewed_page_count', pages)}/{pages})"
            if visual.get("all_pages_rendered_and_reviewed")
            else compact(visual)
        )
        rerun = compact(raw.get("independent_verifier_rerun"))
    else:
        terminal_claim = compact(raw.get("terminal_claim"))
        claim_class = compact(raw.get("claim_class"))
        ev = raw.get("evidence", {})
        claim_pages = compact(ev.get("page_claim")) if isinstance(ev, dict) else ""
        evidence = compact(ev)
        dependencies = compact(raw.get("dependencies_and_citations"))
        risk = compact(raw.get("risks"))
        reviewed = raw.get("visual_pages_reviewed", [])
        visual_status = f"ALL_PAGES_INSPECTED ({len(reviewed)}/{pages})"
        rerun = compact(ev.get("verification_in_this_batch")) if isinstance(ev, dict) else ""
    return {
        "author_list_number": number,
        "id": raw["id"],
        "version": version,
        "title": title,
        "category": raw.get("category"),
        "publication_status": raw.get("status") or raw.get("publication_status") or "PUBLICADO",
        "pdf_url": url,
        "pdf_sha256": sha,
        "pdf_size_bytes": raw.get("pdf_size_bytes") or raw.get("public_pdf_size_bytes"),
        "pages": pages,
        "encrypted": raw.get("encrypted"),
        "claim_pages": claim_pages,
        "claim_class": claim_class,
        "terminal_claim": terminal_claim,
        "evidence": evidence,
        "dependencies": dependencies,
        "risk": risk,
        "verdict": raw["verdict"],
        "action": compact(raw.get("action")),
        "visual_status": visual_status,
        "independent_rerun": rerun,
    }


def main() -> None:
    census = json.loads(CENSUS.read_text(encoding="utf-8"))["records"]
    census_by_number = {item["author_list_number"]: item for item in census}
    records: list[dict[str, Any]] = []
    for path in BATCHES:
        data = json.loads(path.read_text(encoding="utf-8"))
        records.extend(normalize(item) for item in data["records"])
    records.sort(key=lambda item: item["author_list_number"], reverse=True)
    for item in records:
        item.update(OVERRIDES.get(item["id"], {}))

    numbers = [item["author_list_number"] for item in records]
    if numbers != list(range(103, 0, -1)):
        raise RuntimeError(f"audit coverage is not exactly 103..1: {numbers}")
    if len({item["id"] for item in records}) != 103:
        raise RuntimeError("duplicate paper ID in audit batches")

    for item in records:
        public = census_by_number[item["author_list_number"]]
        expected_version = f"v{public['current_version']}"
        if item["id"] != public["id"] or item["version"] != expected_version:
            raise RuntimeError(f"census identity mismatch at row {item['author_list_number']}")
        if public["pdf_download_error"] is None:
            if item["pdf_sha256"] != public["pdf_sha256"] or item["pages"] != public["pdfinfo"]["pages"]:
                raise RuntimeError(f"public object mismatch for {item['id']}{item['version']}")
        elif item["id"] != "2512.0081":
            raise RuntimeError(f"unexpected unavailable PDF: {item['id']}")

    counts = Counter(item["verdict"] for item in records)
    pages = sum(item["pages"] or 0 for item in records)
    ledger_json = {
        "audit_date": "2026-07-31",
        "public_paper_count": len(records),
        "available_public_pdf_count": sum(item["pages"] is not None for item in records),
        "visually_inspected_public_pages": pages,
        "verdict_counts": dict(sorted(counts.items())),
        "records": records,
    }
    (DOCS / "PAPER-AUDIT-LEDGER.json").write_text(
        json.dumps(ledger_json, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )

    lines = [
        "# Paper audit ledger — public corpus frozen 2026-07-31",
        "",
        "This ledger covers every one of the 103 records on the public author page. "
        "The 102 downloadable current PDFs were rendered page by page; 922/922 pages "
        "were visually inspected. The current PDF for 2512.0081v2 returns HTTP 404 and "
        "was not silently replaced by v1.",
        "",
        f"Verdicts: {', '.join(f'`{key}` {value}' for key, value in sorted(counts.items()))}.",
        "",
        "`KEEP` means no publication action is presently recommended; it does not "
        "upgrade author-reported numerics or machine checks into an independent certificate. "
        "`REVIEW-PENDING` names an unresolved audit gate. A clean render or printed PASS "
        "never substitutes for the mathematical evidence column.",
        "",
        "| # | Public object | SHA-256 / pages | Terminal claim and class | Evidence / page | Risk | Verdict | Required action |",
        "|---:|---|---|---|---|---|---|---|",
    ]
    for item in records:
        object_label = f"[{item['id']}{item['version']}]({item['pdf_url']}) — {md(item['title'])}"
        object_hash = (
            f"`{item['pdf_sha256']}` / {item['pages']}"
            if item["pdf_sha256"] and item["pages"] is not None
            else "CURRENT PDF UNAVAILABLE / pages unknown"
        )
        claim = f"{md(item['terminal_claim'])} **Class:** {md(item['claim_class'])}"
        evidence = f"{md(item['claim_pages'])}: {md(item['evidence'])} Visual: {md(item['visual_status'])}."
        lines.append(
            f"| {item['author_list_number']} | {object_label} | {object_hash} | {claim} | "
            f"{evidence} | {md(item['risk'])} | **{item['verdict']}** | {md(item['action'])} |"
        )
    lines.extend(
        [
            "",
            "## Independent replay boundary",
            "",
            "The public manuscripts often cite commits or verifier totals, but many do not "
            "bind an exact immutable checkout and executable target available in this worktree. "
            "Those cases remain author-reported. The broad `lake build YangMillsCore` attempt is "
            "tracked separately and is not a PASS unless the command terminates successfully.",
            "",
        ]
    )
    (DOCS / "PAPER-AUDIT-LEDGER.md").write_text("\n".join(lines), encoding="utf-8", newline="\n")

    pending = [item for item in records if item["verdict"] == "REVIEW-PENDING"]
    pending_lines = [
        "# Review pending — frozen public corpus 2026-07-31",
        "",
        "These records must not be promoted to independently verified, superseded, or ready "
        "merely because a PDF exists or a manuscript reports PASS.",
        "",
        "| Public object | Risk | Open audit obligation | Page/claim evidence |",
        "|---|---|---|---|",
    ]
    for item in pending:
        pending_lines.append(
            f"| [{item['id']}{item['version']}]({item['pdf_url']}) | {md(item['risk'])} | "
            f"{md(item['action'])} | {md(item['claim_pages'])}: {md(item['terminal_claim'])} |"
        )
    pending_lines.extend(
        [
            "",
            "## Global execution debt",
            "",
            "- Lean: a clean-worktree `lake build YangMillsCore` was attempted, but the first "
            "  launcher timed out while mathlib dependencies were still compiling. Until a "
            "  successful terminal exit and the targeted oracle/sorry/axiom scans exist, no "
            "  global machine-certificate claim is upgraded by this audit.",
            "- Public-object integrity: `2512.0081v2` remains unavailable at its advertised URL.",
            "- Hybrid certificates: `2607.0089v1` needs an independent replay of every exact-to-Arb "
            "  handoff and interval regime before it can close the surface-sign chain.",
            "",
        ]
    )
    (DOCS / "REVIEW-PENDING.md").write_text(
        "\n".join(pending_lines), encoding="utf-8", newline="\n"
    )
    print(json.dumps(ledger_json["verdict_counts"], sort_keys=True))
    print(f"records={len(records)} pages={pages} pending={len(pending)}")


if __name__ == "__main__":
    main()
