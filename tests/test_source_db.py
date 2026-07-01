from __future__ import annotations

import importlib.util
import re
import sqlite3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("source_db", ROOT / "scripts" / "source_db.py")
assert SPEC and SPEC.loader
source_db = importlib.util.module_from_spec(SPEC)
import sys
sys.modules[SPEC.name] = source_db
SPEC.loader.exec_module(source_db)

CONTROL_ESCAPE = re.compile(r"\\u00(?:0[0-9a-fA-F]|1[0-9a-fA-F])")


def test_catalogs_validate() -> None:
    records = source_db.load_catalogs(ROOT)
    assert source_db.validate_catalogs(records, ROOT) == []


def test_dictionary_link_structure_validates(tmp_path: Path) -> None:
    record = source_db.CatalogRecord(
        path=tmp_path / "catalog.json",
        data={
            "sources": {"test_source": {"short": "TEST", "title": "Synthetic test source"}},
            "citations": [
                {
                    "key": "test.bad-dictionary-link",
                    "source_id": "test_source",
                    "locator": {"printed_pages": "1", "pdf_pages": "1"},
                    "status": "located",
                    "summary": "Synthetic malformed dictionary-link record.",
                    "dictionary_links": [
                        {
                            "id": "test.duplicate-link",
                            "source_symbol": "source symbol",
                            "relation": "candidate_context_for",
                            "status": "",
                            "discharged_by": "",
                        },
                        {
                            "id": "test.duplicate-link",
                            "source_symbol": "another source symbol",
                            "lean_symbol": "LeanSymbol",
                            "status": "dictionary_open",
                        },
                    ],
                }
            ],
        },
    )

    errors = source_db.validate_catalogs([record], tmp_path)

    assert "test.bad-dictionary-link: dictionary_links[1].lean_symbol missing" in "\n".join(errors)
    assert "test.bad-dictionary-link: dictionary_links[1].status must be a non-empty string" in "\n".join(errors)
    assert "test.bad-dictionary-link: dictionary_links[1].discharged_by must be a non-empty string" in "\n".join(errors)
    assert "test.bad-dictionary-link: duplicate dictionary link id test.duplicate-link" in "\n".join(errors)


def test_source_metadata_has_no_control_escapes() -> None:
    roots = [
        ROOT / "docs" / "source-db",
        ROOT / "docs" / "idea-db" / "ym-creative-expansion",
    ]
    suffixes = {".json", ".jsonl"}
    offenders: list[str] = []

    for root in roots:
        for path in sorted(p for p in root.rglob("*") if p.suffix.lower() in suffixes):
            text = path.read_text(encoding="utf-8")
            escaped = sorted(set(CONTROL_ESCAPE.findall(text)))
            actual = sorted({f"U+{ord(ch):04X}" for ch in text if ord(ch) < 32 and ch not in "\r\n\t"})
            if escaped or actual:
                rel = path.relative_to(ROOT).as_posix()
                offenders.append(f"{rel}: escaped={escaped} actual={actual}")

    assert offenders == []


def test_database_builds(tmp_path: Path) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    assert output.exists()
    with sqlite3.connect(output) as conn:
        assert conn.execute("select count(*) from sources").fetchone()[0] >= 10
        assert conn.execute("select count(*) from citations").fetchone()[0] >= 15
        assert conn.execute("select count(*) from claims").fetchone()[0] >= 8
        row = conn.execute(
            "select status from citations where citation_key='cmp116.eq231.p-family-carrier-source-target'"
        ).fetchone()
        assert row == ("source_pending",)


def test_database_indexes_every_catalog_key(tmp_path: Path) -> None:
    output = tmp_path / "index.sqlite"
    records = source_db.load_catalogs(ROOT)
    expected = {citation["key"] for _, citation in source_db.iter_citations(records, ROOT)}
    source_db.build_database(output=output, root=ROOT)
    with sqlite3.connect(output) as conn:
        actual = {row[0] for row in conn.execute("select citation_key from citations")}
    assert actual == expected
    assert "proof.eq231.source-package.live-fields.v2" in actual


def test_show_prints_dictionary_links(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.eq231.source-package.live-fields.v2", path=output)
    captured = capsys.readouterr()
    assert "dictionary links:" in captured.out
    assert "CMP116Eq231BalabanPFamilySourcePackage" in captured.out


def test_search_indexes_dictionary_link_symbols(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("CMP119BLocalSourceMetricStaging", path=output)
    captured = capsys.readouterr()
    assert "cmp119.eq2.42.blocal-bound-source-target" in captured.out
    assert "B/local component decay" in captured.out


def test_search_indexes_dictionary_link_discharged_by(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("CMP119BLocalSourceMetricStaging.to_metricDictionary", path=output)
    captured = capsys.readouterr()
    assert "cmp119.eq2.42.blocal-bound-source-target" in captured.out
    assert "B/local component decay" in captured.out


def test_lean_prints_dictionary_link_matches(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("CMP119BLocalSourceMetricStaging", path=output)
    captured = capsys.readouterr()
    assert "CMP119BLocalSourceMetricStaging <- cmp119.eq2.42.blocal-bound-source-target" in captured.out
    assert "dictionary link: staging_interface/lean_linked" in captured.out
    assert "does not define d_j(X)" in captured.out
    assert "discharged_by: YangMills.RG.CMP119BLocalSourceMetricStaging;" in captured.out
    assert "YangMills.RG.CMP119BLocalSourceMetricStaging.to_metricDictionary" in captured.out


def test_show_prints_direct_source_acquisition_paths(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("cmp116.eq231.p-family-carrier-source-target", path=output)
    captured = capsys.readouterr()
    assert "source acquisition:" in captured.out
    assert "source root:" in captured.out
    assert "balaban-rg-II-cmp116-1104161193.pdf" in captured.out


def test_artifacts_prints_cammarota_acquisition_paths(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_artifacts("cammarota_cmp85", path=output)
    captured = capsys.readouterr()
    assert "project_euclid_pdf" in captured.out
    assert "cammarota_cmp85/cammarota-cmp85.pdf" in captured.out
    assert "cammarota_cmp85/text/cammarota-cmp85.txt" in captured.out
    assert "[missing]" in captured.out


def test_frontier_prints_lean_linked_open_questions(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="rawsource", status="lean_linked", limit=5, path=output)
    captured = capsys.readouterr()
    assert "proof.rawsource.m3.live-fields.v2 [lean_linked]" in captured.out
    assert "targets=" in captured.out
    assert "questions=" in captured.out
    assert "Exact source dictionary" in captured.out


def test_head_refs_prints_source_metadata_commit_anchors(capsys) -> None:
    source_db.print_head_refs(root=ROOT)
    captured = capsys.readouterr()
    assert "current HEAD:" in captured.out
    assert "1fed14e" in captured.out
    assert "[ancestor]" in captured.out or "[current]" in captured.out


def test_metadata_packet(tmp_path: Path) -> None:
    output = tmp_path / "packet.zip"
    source_db.build_packet(output=output, include_raw=False, root=ROOT)
    assert output.exists()
