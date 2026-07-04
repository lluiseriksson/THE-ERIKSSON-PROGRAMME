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


def test_coverage_structure_validates(tmp_path: Path) -> None:
    record = source_db.CatalogRecord(
        path=tmp_path / "catalog.json",
        data={
            "sources": {"test_source": {"short": "TEST", "title": "Synthetic test source"}},
            "coverage": [
                {
                    "source_id": "test_source",
                    "importance": "high",
                    "catalog_status": "",
                    "artifact_status": "present",
                    "formula_status": "minimal",
                    "next_action": "Keep the synthetic row honest.",
                    "priority": "7",
                },
                {
                    "source_id": "test_source",
                    "importance": "high",
                    "catalog_status": "seeded",
                    "artifact_status": "present",
                    "formula_status": "minimal",
                    "next_action": "Duplicate source id.",
                    "priority": 7,
                },
            ],
        },
    )

    errors = source_db.validate_catalogs([record], tmp_path)

    joined = "\n".join(errors)
    assert "coverage[1].catalog_status must be a non-empty string" in joined
    assert "coverage[1].priority must be an integer" in joined
    assert "duplicate coverage source_id test_source" in joined


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


def test_frontier_finds_cmp122_r_operation_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="cmp122", status="lean_linked", limit=30, path=output)
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "targets=7" in captured.out
    assert "questions=6" in captured.out
    assert "CMP122-II Theorem 1 small-coupling hypotheses" in captured.out


def test_lean_lookup_finds_cmp122_source_dictionary_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("CMP119CMP122ERBSourceDecomposition", path=output)
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "CMP122-I/II and CMP119 localized R-operation bounds" in captured.out


def test_search_finds_cmp122_post_r_action_dictionary(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("post-r action", path=output)
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "Source anchor for the post-R E/R/B update" in captured.out


def test_frontier_finds_eq237_fixed_z0prime_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="eq237", status="lean_linked", limit=20, path=output)
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out
    assert "targets=12" in captured.out
    assert "questions=4" in captured.out
    assert "D/P/Z0/Z0' dictionaries" in captured.out


def test_lean_lookup_finds_eq237_source_dictionary_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("cmp116Eq237Z0Fiber", path=output)
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out
    assert "CMP116 Eq. (2.37) fixed-Z0' source estimate" in captured.out


def test_search_finds_eq237_combined_postp_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("cmp116PostPResidualSourceBound_of_eq237", path=output)
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out
    assert "CMP116 Eq. (2.37) fixed-Z0' source estimate" in captured.out


def test_frontier_finds_eq229_cammarota_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="eq229", status="lean_linked", limit=20, path=output)
    captured = capsys.readouterr()
    assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in captured.out
    assert "targets=13" in captured.out
    assert "questions=4" in captured.out
    assert "Cammarota theorem statement" in captured.out


def test_lean_lookup_finds_eq229_cammarota_source_interface(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("CammarotaCMP85FiniteDStageSource", path=output)
    captured = capsys.readouterr()
    assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in captured.out
    assert "CMP116 Eq. (2.29) D-stage product summability via Cammarota CMP85" in captured.out


def test_search_finds_eq229_scale_boundary_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("CMP116Lemma3Eq229ScaleBoundary", path=output)
    captured = capsys.readouterr()
    assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in captured.out
    assert "CMP116 Eq. (2.29) D-stage product summability via Cammarota CMP85" in captured.out


def test_frontier_finds_activity_termwise_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="activity", status="lean_linked", limit=30, path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "targets=3" in captured.out
    assert "questions=5" in captured.out
    assert "source-to-Lean index-stack identification for H(Z,Z0)/H(Z)" in captured.out


def test_search_finds_activity_termwise_boundary(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("CMP116Lemma3ActivityTermwiseScaleBoundary", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "CMP116 H(Z) activity identification and termwise estimate" in captured.out


def test_frontier_finds_gaussian_covariance_root_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="gaussian", status="lean_linked", limit=30, path=output)
    captured = capsys.readouterr()
    assert "proof.gaussian.covariance-root-certificate.v2 [lean_linked]" in captured.out
    assert "targets=4" in captured.out
    assert "questions=3" in captured.out
    assert "Exact operator equality/inequality fields" in captured.out


def test_search_finds_gaussian_covariance_root_certificate(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("PhysicalLocalizedCovarianceRootCertificate", path=output)
    captured = capsys.readouterr()
    assert "proof.gaussian.covariance-root-certificate.v2 [lean_linked]" in captured.out
    assert "finite/physical covariance-root certificate" in captured.out


def test_search_finds_root_localization_field(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("root_localization", path=output)
    captured = capsys.readouterr()
    assert "proof.root.localization.v2 [lean_linked]" in captured.out
    assert "Live-field card for root localization" in captured.out


def test_search_finds_physical_precision_defect_hdefect_blocker(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("physicalPrecisionDefect hdefect", path=output)
    captured = capsys.readouterr()
    assert "proof.wilson.hessian.identification.v2 [lean_linked]" in captured.out
    assert "Wilson-Hessian interface" in captured.out
    assert "source-to-Lean coordinate, sign and normalization dictionary" in captured.out


def test_frontier_finds_activity_support_measurability_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="support", status="lean_linked", limit=30, path=output)
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "targets=5" in captured.out
    assert "questions=3" in captured.out
    assert "Exact enlargement convention" in captured.out


def test_search_finds_physical_active_support_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("physicalActiveSupport", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "Live-field card for support containment and measurability" in captured.out


def test_frontier_finds_appendixf_hsharp_feed_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="appendixf", status="lean_linked", limit=30, path=output)
    captured = capsys.readouterr()
    assert "proof.dimock.appendixf.hsharp-feed [lean_linked]" in captured.out
    assert "targets=3" in captured.out
    assert "questions=3" in captured.out
    assert "activity/locality estimate" in captured.out


def test_search_finds_appendixf_hsharp_route(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("hsharp", path=output)
    captured = capsys.readouterr()
    assert "proof.dimock.appendixf.hsharp-feed [lean_linked]" in captured.out
    assert "Dimock Appendix F H# route into hole-cluster machinery" in captured.out


def test_frontier_finds_flow_ir_bridge_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="flow", status="lean_linked", limit=30, path=output)
    captured = capsys.readouterr()
    assert "proof.flow.ir.bridge [lean_linked]" in captured.out
    assert "targets=4" in captured.out
    assert "questions=3" in captured.out
    assert "CMP109/CMP119 beta-function source" in captured.out


def test_search_finds_flow_ir_bridge_route(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("ir bridge", path=output)
    captured = capsys.readouterr()
    assert "proof.flow.ir.bridge [lean_linked]" in captured.out
    assert "Flow and IR bridge separating marginal logarithmic flow" in captured.out


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
