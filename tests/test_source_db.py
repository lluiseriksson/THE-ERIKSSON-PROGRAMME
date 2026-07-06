from __future__ import annotations

import json
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


def test_cmp122_indices_keep_qualified_lean_targets() -> None:
    expected_main = [
        "YangMills.RG.RawYMActivityDecay",
        "YangMills.RG.CMP116RawSourceM3Frontier",
        "YangMills.RG.CMP119CMP122ERBSourceDecomposition",
    ]
    expected = [
        *expected_main,
        "YangMills.RG.CMP116Lemma3DeltaRlocSourceEstimates.to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_weightTransport_amplitudeAndActivityDictionaries",
    ]
    proof_key = "proof.cmp122.r-operation-polymer-local-bound"
    crosswalk_source_key = "crosswalk.r-operation-polymer-local-route"
    source_keys = [
        "cmp119.r-term-bound.2.31",
        "cmp122i.large-field-c-bound.1.70",
        "cmp122ii.rprime-bound.1.98-1.100",
        crosswalk_source_key,
    ]
    source_expected = [
        "YangMills.RG.RawYMActivityDecay",
        "YangMills.RG.CMP116RawSourceM3Frontier",
        "YangMills.lattice_mass_gap_of_per_scale_uv",
    ]
    consumer_live_field_targets = [
        "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.rloc_decay",
        "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.decomposes",
        "YangMills.RG.CMP119CMP122ERBDecomposition",
        "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
    ]
    stale_source_targets = [
        "RawYMActivityDecay",
        "CMP116RawSourceM3Frontier",
        "lattice_mass_gap_of_per_scale_uv",
    ]

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    catalog_card = next(card for card in catalog["citations"] if card["key"] == proof_key)
    assert catalog_card["lean_targets"][: len(expected_main)] == expected_main
    assert expected[-1] in catalog_card["lean_targets"]

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["lean_targets"] == expected

    router = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "source-key-router.json")
        .read_text(encoding="utf-8")
    )
    for source_key in source_keys:
        route = next(
            route
            for route in router["routes"][source_key]
            if route["proof_card"] == proof_key
        )
        assert route["lean_targets"] == expected

    source_catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "llm-operational-crosswalk.json")
        .read_text(encoding="utf-8")
    )
    source_entry = next(
        citation
        for citation in source_catalog["citations"]
        if citation["key"] == crosswalk_source_key
    )
    assert source_entry["lean_targets"] == source_expected
    for target in stale_source_targets:
        assert target not in source_entry["lean_targets"]

    lean_crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    for target in source_expected:
        assert target in lean_crosswalk["targets"]
        assert any(
            item["citation_key"] == crosswalk_source_key
            for item in lean_crosswalk["targets"][target]
        )
    for target in stale_source_targets:
        assert all(
            item["citation_key"] != crosswalk_source_key
            for item in lean_crosswalk["targets"].get(target, [])
        )

    lean_crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    for target in source_expected:
        assert f"| `{target}` | `{crosswalk_source_key}` |" in lean_crosswalk_md
    for target in stale_source_targets:
        assert f"| `{target}` | `{crosswalk_source_key}` |" not in lean_crosswalk_md

    expected_md_line = (
        "- Lean: `YangMills.RG.RawYMActivityDecay`, "
        "`YangMills.RG.CMP116RawSourceM3Frontier`, "
        "`YangMills.RG.CMP119CMP122ERBSourceDecomposition`, "
        "`YangMills.RG.CMP116Lemma3DeltaRlocSourceEstimates.to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_weightTransport_amplitudeAndActivityDictionaries`"
    )
    source_router_md = (
        ROOT / "docs" / "source-db" / "indices" / "SOURCE-KEY-ROUTER.md"
    ).read_text(encoding="utf-8")
    assert expected_md_line in source_router_md

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    assert "  - YangMills.RG.RawYMActivityDecay" in proof_cards_md
    assert "  - YangMills.RG.CMP116RawSourceM3Frontier" in proof_cards_md
    assert "  - YangMills.RG.CMP119CMP122ERBSourceDecomposition" in proof_cards_md
    assert (
        "  - YangMills.RG.CMP116Lemma3DeltaRlocSourceEstimates."
        "to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_"
        "weightTransport_amplitudeAndActivityDictionaries"
        in proof_cards_md
    )

    live_fields_md = (
        ROOT / "docs" / "source-db" / "indices" / "CMP122-R-OPERATION-LIVE-FIELDS.md"
    ).read_text(encoding="utf-8")
    for target in expected_main:
        assert f"`{target}`" in live_fields_md
    for target in consumer_live_field_targets:
        assert f"`{target}`" in live_fields_md
    assert "`CMP119CMP122ERBSourceDecomposition`" not in live_fields_md
    assert "`CMP116RawSourceM3Frontier`" not in live_fields_md
    assert "`RawYMActivityDecay` route only after dictionaries" not in live_fields_md
    assert "future source certificate for `rloc_decay`" not in live_fields_md
    assert "source metric/domain dictionary" not in live_fields_md
    assert "local R component decay input" not in live_fields_md
    assert "post-R action/local-activity dictionary" not in live_fields_md
    assert "B/local or component dictionary context" not in live_fields_md
    assert "infer `RawYMActivityDecay`" not in live_fields_md
    assert (
        "`YangMills.RG.PhysicalGaugeLocalActivity.globalEval` equality"
        in live_fields_md
    )

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md

    source_citations = json.loads(
        (ROOT / "docs" / "source-citations" / "cmp116-lemma3.json").read_text(
            encoding="utf-8"
        )
    )
    cmp122_erb_source_keys = [
        "cmp119.r-term-bound.2.31",
        "cmp119.density-expansion-form.2.18",
        "cmp119.t-operation-action-factorization.2.19-2.23",
        "cmp119.e-term-local-regularity.2.24-2.29",
    ]
    for source_key in cmp122_erb_source_keys:
        citation = next(
            citation
            for citation in source_citations["citations"]
            if citation["key"] == source_key
        )
        assert (
            "YangMills.RG.CMP119CMP122ERBSourceDecomposition"
            in citation["lean_targets"]
        )
        assert "CMP119CMP122ERBSourceDecomposition" not in citation["lean_targets"]

    blocal_citation = next(
        citation
        for citation in source_citations["citations"]
        if citation["key"] == "cmp119.b-term-local-regularity-bound.2.34-2.42"
    )
    assert "YangMills.RG.CMP119BLocalSourceBound" in blocal_citation["lean_targets"]
    assert "CMP119BLocalSourceBound" not in blocal_citation["lean_targets"]


def test_cmp122_proof_card_indices_record_extraction_blocker_status() -> None:
    proof_key = "proof.cmp122.r-operation-polymer-local-bound"
    expected_status = "located_not_fully_extracted"

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["status"] == expected_status

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    assert f"## 9. `{proof_key}`" in proof_cards_md
    assert f"**Status:** `{expected_status}`" in proof_cards_md


def test_cmp119_inductive_density_anchor_keeps_qualified_lean_targets(
    tmp_path: Path,
) -> None:
    source_key = "cmp119.eq2.17-2.18.inductive-density-source-target"
    expected = [
        "YangMills.RG.CMP119BLocalActivityIdentificationDictionary.bloc_identification",
        "YangMills.RG.CMP119CMP122ERBSourceDecomposition",
    ]
    stale = [
        "CMP119BLocalActivityIdentificationDictionary.bloc_identification",
        "CMP119CMP122ERBSourceDecomposition",
    ]

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "spine-backlog.json").read_text(
            encoding="utf-8"
        )
    )
    catalog_card = next(
        citation for citation in catalog["citations"] if citation["key"] == source_key
    )
    assert catalog_card["lean_targets"] == expected
    for target in stale:
        assert target not in catalog_card["lean_targets"]

    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    with sqlite3.connect(output) as conn:
        indexed_targets = [
            row[0]
            for row in conn.execute(
                """
                select lean_target from lean_targets
                where citation_key = ?
                order by ordinal
                """,
                (source_key,),
            )
        ]
    assert indexed_targets == expected
    for target in stale:
        assert target not in indexed_targets


def test_cmp122_live_field_source_anchors_keep_qualified_targets(
    tmp_path: Path,
) -> None:
    expected_by_source = {
        "cmp122i.eq1.70.large-field-bound-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
        ],
        "cmp122ii.eq1.70.blocal-bound-source-target": [
            "YangMills.RG.CMP119BLocalActivityIdentificationDictionary.bloc_identification",
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
        ],
        "cmp122ii.eq1.98-1.100.r-operation-bound-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.rloc_decay",
        ],
        "cmp122ii.eq1.101.post-r-erb-update-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.decomposes",
        ],
    }
    stale_by_source = {
        "cmp122i.eq1.70.large-field-bound-source-target": [
            "PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
        ],
        "cmp122ii.eq1.70.blocal-bound-source-target": [
            "CMP119BLocalActivityIdentificationDictionary.bloc_identification",
            "PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
        ],
        "cmp122ii.eq1.98-1.100.r-operation-bound-source-target": [
            "PhysicalGaugeDimock318ERBComponentBoundary.rloc_decay",
        ],
        "cmp122ii.eq1.101.post-r-erb-update-source-target": [
            "PhysicalGaugeDimock318ERBComponentBoundary.decomposes",
        ],
    }

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "spine-backlog.json").read_text(
            encoding="utf-8"
        )
    )
    citations = {citation["key"]: citation for citation in catalog["citations"]}
    for source_key, expected in expected_by_source.items():
        assert citations[source_key]["lean_targets"] == expected
        for target in stale_by_source[source_key]:
            assert target not in citations[source_key]["lean_targets"]

    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    with sqlite3.connect(output) as conn:
        for source_key, expected in expected_by_source.items():
            indexed_targets = [
                row[0]
                for row in conn.execute(
                    """
                    select lean_target from lean_targets
                    where citation_key = ?
                    order by ordinal
                    """,
                    (source_key,),
                )
            ]
            assert indexed_targets == expected
            for target in stale_by_source[source_key]:
                assert target not in indexed_targets

    crosswalk = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json")
        .read_text(encoding="utf-8")
    )["targets"]
    crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    for source_key, expected in expected_by_source.items():
        for target in expected:
            assert any(row["citation_key"] == source_key for row in crosswalk[target])
            assert f"| `{target}` | `{source_key}` |" in crosswalk_md
        for target in stale_by_source[source_key]:
            assert not any(
                row["citation_key"] == source_key for row in crosswalk.get(target, [])
            )
            assert f"| `{target}` | `{source_key}` |" not in crosswalk_md


def test_cmp119_cmp116_erbs_source_anchors_keep_qualified_targets(
    tmp_path: Path,
) -> None:
    expected_by_source = {
        "cmp119.eq2.29-2.33.blocal-component-source-target": [
            "YangMills.RG.CMP119BLocalActivityIdentificationDictionary.bloc_identification",
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
        ],
        "cmp119.eq2.23.erb-decomposition-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.decomposes",
        ],
        "cmp119.eq2.42.blocal-bound-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
            "YangMills.RG.CMP119BLocalMetricDictionary",
            "YangMills.RG.CMP119BLocalToLemma3WeightTransport.rate_margin",
            "bloc_identification",
        ],
        "cmp116.lemma3.eq2.38.component-decay-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.deltaE_decay",
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.rloc_decay",
        ],
    }
    stale_by_source = {
        "cmp119.eq2.29-2.33.blocal-component-source-target": [
            "CMP119BLocalActivityIdentificationDictionary.bloc_identification",
            "PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
        ],
        "cmp119.eq2.23.erb-decomposition-source-target": [
            "PhysicalGaugeDimock318ERBComponentBoundary.decomposes",
        ],
        "cmp119.eq2.42.blocal-bound-source-target": [
            "PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
            "CMP119BLocalMetricDictionary",
            "CMP119BLocalToLemma3WeightTransport.rate_margin",
        ],
        "cmp116.lemma3.eq2.38.component-decay-source-target": [
            "PhysicalGaugeDimock318ERBComponentBoundary.deltaE_decay",
            "PhysicalGaugeDimock318ERBComponentBoundary.rloc_decay",
        ],
    }
    expected_links_by_source = {
        "cmp119.eq2.29-2.33.blocal-component-source-target": [
            "YangMills.RG.CMP119BLocalActivityIdentificationDictionary.bloc_identification",
        ],
        "cmp119.eq2.23.erb-decomposition-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.decomposes",
        ],
        "cmp119.eq2.42.blocal-bound-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
            "YangMills.RG.CMP119BLocalMetricDictionary",
            "YangMills.RG.CMP119BLocalToLemma3WeightTransport.rate_margin",
        ],
        "cmp116.lemma3.eq2.38.component-decay-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.deltaE_decay",
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.rloc_decay",
            "YangMills.RG.CMP119BLocalActivityIdentificationDictionary.bloc_identification",
        ],
    }
    static_crosswalk_expected_by_source = {
        "cmp119.eq2.23.erb-decomposition-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.decomposes",
        ],
        "cmp119.eq2.42.blocal-bound-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.bloc_decay",
        ],
        "cmp116.lemma3.eq2.38.component-decay-source-target": [
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.deltaE_decay",
            "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.rloc_decay",
        ],
    }

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "spine-backlog.json").read_text(
            encoding="utf-8"
        )
    )
    citations = {citation["key"]: citation for citation in catalog["citations"]}
    for source_key, expected in expected_by_source.items():
        assert citations[source_key]["lean_targets"] == expected
        link_symbols = {
            link["lean_symbol"] for link in citations[source_key]["dictionary_links"]
        }
        for target in expected_links_by_source[source_key]:
            assert target in link_symbols
        for target in stale_by_source[source_key]:
            assert target not in citations[source_key]["lean_targets"]
            assert target not in link_symbols

    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    with sqlite3.connect(output) as conn:
        for source_key, expected in expected_by_source.items():
            indexed_targets = [
                row[0]
                for row in conn.execute(
                    """
                    select lean_target from lean_targets
                    where citation_key = ?
                    order by ordinal
                    """,
                    (source_key,),
                )
            ]
            assert indexed_targets == expected
            for target in stale_by_source[source_key]:
                assert target not in indexed_targets

    crosswalk = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json")
        .read_text(encoding="utf-8")
    )["targets"]
    crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    for source_key, expected in static_crosswalk_expected_by_source.items():
        for target in expected:
            assert any(row["citation_key"] == source_key for row in crosswalk[target])
            assert f"| `{target}` | `{source_key}` |" in crosswalk_md
        for target in stale_by_source[source_key]:
            assert not any(
                row["citation_key"] == source_key for row in crosswalk.get(target, [])
            )
            assert f"| `{target}` | `{source_key}` |" not in crosswalk_md


def test_cmp122_proof_card_keeps_split_certificate_next_action() -> None:
    proof_key = "proof.cmp122.r-operation-polymer-local-bound"
    expected_next_action = (
        "Extract each source-certificate field separately: CMP122-II Theorem 1 handoff, "
        "R' bounds, post-R split, CMP122-I C_k bound, CMP119 E/R/B handoff, and the "
        "explicit post-R action/local-activity dictionary."
    )
    expected_dependencies = [
        "CMP122-II Theorem 1 small-coupling and CMP119 Sect. 2 handoff",
        "CMP122-II (1.98)-(1.100) R' expansion and bounds",
        "CMP122-II (1.101)-(1.102) post-R action split",
        "CMP122-I (1.70) large-field C_k bound",
        "CMP119 E/R/B and R/B local-regularity handoff",
        "source-to-Lean post-R action/local-activity dictionary",
    ]

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["next_action"] == expected_next_action
    assert indexed_card["dependencies"] == expected_dependencies
    assert "RawYMActivityDecay proof" not in indexed_card["next_action"]

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    assert f"**Next action:** {expected_next_action}" in proof_cards_md
    for dependency in expected_dependencies:
        assert f"  - {dependency}" in proof_cards_md


def test_hypothesis_queue_keeps_cmp122_r_operation_open_gate() -> None:
    proof_key = "proof.cmp122.r-operation-polymer-local-bound"
    expected_live_hypotheses = [
        "RawYMActivityDecay",
        "polymer-local R/B/C source bounds",
        "large-field dictionary",
        "post-R action/local-activity dictionary",
    ]
    expected_source_keys = [
        "cmp119.density-expansion-form.2.18",
        "cmp119.t-operation-action-factorization.2.19-2.23",
        "cmp119.e-term-local-regularity.2.24-2.29",
        "cmp119.r-term-bound.2.31",
        "cmp119.b-term-local-regularity-bound.2.34-2.42",
        "cmp119.rt-improved-new-expressions.before-theorem1",
        "cmp119.theorem1.rt-inductive-assumptions",
        "cmp122ii.theorem1.coupling-interval-induction",
        "cmp122i.large-field-c-bound.1.70",
        "cmp122ii.rprime-bound.1.98-1.100",
        "cmp122ii.post-r-action-split.1.101",
        "crosswalk.r-operation-polymer-local-route",
    ]
    expected_lean_targets = [
        "RawYMActivityDecay",
        "CMP116RawSourceM3Frontier",
    ]
    expected_next_action = (
        "Extract each source-certificate field separately: CMP122-II Theorem 1 handoff, "
        "R' bounds, post-R split, CMP122-I C_k bound, CMP119 E/R/B handoff, and the "
        "explicit post-R action/local-activity dictionary."
    )

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["rank"] == 9
    assert queued_card["live_hypotheses"] == expected_live_hypotheses
    assert queued_card["source_keys"] == expected_source_keys
    assert queued_card["lean_targets"] == expected_lean_targets
    assert queued_card["next_action"] == expected_next_action
    assert any(
        blocker.startswith("surrogate scalar R_k <= M r^k")
        for blocker in queued_card["removes"]
    )

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    assert (
        f"| 9 | `{proof_key}` | RawYMActivityDecay plus post-R "
        "action/local-activity dictionary |"
        in hypothesis_queue_md
    )
    assert "`cmp122ii.post-r-action-split.1.101`" in hypothesis_queue_md
    assert "`YangMills.RG.CMP116RawSourceM3Frontier`" in hypothesis_queue_md


def test_cmp122_theorem1_spine_entry_keeps_qualified_lean_targets(
    tmp_path: Path, capsys
) -> None:
    source_key = "cmp122ii.theorem1.coupling-interval-induction"
    expected = [
        "YangMills.RG.RawYMActivityDecay",
        "YangMills.RG.CMP116RawSourceM3Frontier",
    ]
    stale = [
        "RawYMActivityDecay",
        "CMP116RawSourceM3Frontier",
    ]

    spine_catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "spine-backlog.json")
        .read_text(encoding="utf-8")
    )
    source_entry = next(
        citation for citation in spine_catalog["citations"] if citation["key"] == source_key
    )
    assert source_entry["lean_targets"] == expected
    for target in stale:
        assert target not in source_entry["lean_targets"]

    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    for target in expected:
        source_db.print_lean(target, path=output)
        captured = capsys.readouterr()
        assert f"{target} <- {source_key} [visual_confirmed]" in captured.out


def test_eq237_indices_keep_qualified_lean_targets() -> None:
    expected = [
        "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
        "YangMills.RG.CMP116Eq237MajorizationBoundary",
        "YangMills.RG.cmp116Eq237FixedZ0PrimeWeight",
        "YangMills.RG.cmp116Eq237Amplitude",
    ]
    proof_key = "proof.eq237.fixed-z0prime-source-estimate"
    crosswalk_source_key = "crosswalk.eq237.combined-postp-route"
    source_keys = [
        "cmp116.eq237.post-p-resummation",
        "cmp116.constants.c3-alpha5",
        crosswalk_source_key,
    ]
    source_expected = [
        "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
        "YangMills.RG.CMP116Eq237MajorizationBoundary",
        "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
    ]
    stale_source_targets = [
        "cmp116PostPResidualSourceBound_of_eq237",
        "CMP116Eq237MajorizationBoundary",
        "CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
    ]

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    catalog_card = next(card for card in catalog["citations"] if card["key"] == proof_key)
    for target in expected:
        assert target in catalog_card["lean_targets"]

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["lean_targets"] == expected

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["lean_targets"] == expected

    router = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "source-key-router.json")
        .read_text(encoding="utf-8")
    )
    for source_key in source_keys:
        route = next(
            route
            for route in router["routes"][source_key]
            if route["proof_card"] == proof_key
        )
        assert route["lean_targets"] == expected

    source_catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "llm-operational-crosswalk.json")
        .read_text(encoding="utf-8")
    )
    source_entry = next(
        citation
        for citation in source_catalog["citations"]
        if citation["key"] == crosswalk_source_key
    )
    assert source_entry["lean_targets"] == source_expected
    for target in stale_source_targets:
        assert target not in source_entry["lean_targets"]

    lean_crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    for target in source_expected:
        assert target in lean_crosswalk["targets"]
        assert any(
            item["citation_key"] == crosswalk_source_key
            for item in lean_crosswalk["targets"][target]
        )
    for target in stale_source_targets:
        assert all(
            item["citation_key"] != crosswalk_source_key
            for item in lean_crosswalk["targets"].get(target, [])
        )

    lean_crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    for target in source_expected:
        assert f"| `{target}` | `{crosswalk_source_key}` |" in lean_crosswalk_md
    for target in stale_source_targets:
        assert f"| `{target}` | `{crosswalk_source_key}` |" not in lean_crosswalk_md

    expected_md_line = (
        "- Lean: `YangMills.RG.cmp116PostPResidualSourceBound_of_eq237`, "
        "`YangMills.RG.CMP116Eq237MajorizationBoundary`, "
        "`YangMills.RG.cmp116Eq237FixedZ0PrimeWeight`, "
        "`YangMills.RG.cmp116Eq237Amplitude`"
    )
    source_router_md = (
        ROOT / "docs" / "source-db" / "indices" / "SOURCE-KEY-ROUTER.md"
    ).read_text(encoding="utf-8")
    assert expected_md_line in source_router_md

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"  - {target}" in proof_cards_md

    live_fields_md = (
        ROOT / "docs" / "source-db" / "indices" / "EQ237-POSTP-LIVE-FIELDS.md"
    ).read_text(encoding="utf-8")
    live_field_targets = [
        "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
        "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237_globalIndex",
        "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237_sourceIndexMemIff",
        "YangMills.RG.CMP116Lemma3WeightedPostPSourceScaleBoundary.of_eq237",
        "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
        "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237",
        "YangMills.RG.cmp116Eq237Z0PrimeIndex_subset_global",
        "YangMills.RG.CMP116PostPResidualSourceBound",
        "YangMills.RG.CMP116PostPResidualSourceMajorizationScaleFamily",
    ]
    live_field_rows = [
        (
            "| `heq237_fixed` | fixed-`Z0'` Eq. (2.37) source estimate | "
            "`proof.eq237.fixed-z0prime-display.v2` | "
            "`YangMills.RG.cmp116PostPResidualSourceBound_of_eq237` |"
        ),
        (
            "| `hpost_eq237` | post-(2.37) final summation over `Z0'` / "
            "`Z \\ Z0'` | `proof.eq237.post-summation.final-z0prime.v2` | "
            "`YangMills.RG.cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237` |"
        ),
        (
            "| `dict_Z0_Z0prime` | source-to-Lean dictionary for "
            "`D/P/Z0/Z0'` and fibers | `proof.eq237.z0-z0prime-dictionary.v2` | "
            "`YangMills.RG.cmp116Eq237Z0Fiber`; "
            "`YangMills.RG.cmp116Eq237_nested_sum_eq_fiber_sum` |"
        ),
        (
            "| `component_product` | product over connected components `Z_i'` | "
            "`proof.eq237.component-product-to-family.v2` | "
            "`YangMills.RG.cmp116Eq237FixedZ0PrimeWeight`; "
            "`YangMills.RG.cmp116Eq237Amplitude` |"
        ),
        (
            "| `constant_majorants` | `alpha5`, `epsilon2`, `O(1)`, `C3` "
            "majorization | `proof.eq237.constant-majorants.alpha5-c3.v2` | "
            "`YangMills.RG.CMP116Eq237MajorizationBoundary`; "
            "`YangMills.RG.cmp116Eq237Amplitude` |"
        ),
        (
            "| `residual_budget` | seven-delta to eight-delta exponent reserve | "
            "`proof.eq237.residual-exponent-budget.v2` | "
            "`YangMills.RG.cmp116Eq237_residualExponent_absorbed` |"
        ),
    ]
    stale_live_field_lines = [
        "cmp116PostPResidualSourceBound_of_eq237",
        "cmp116PostPResidualSourceBound_of_eq237_globalIndex",
        "cmp116PostPResidualSourceBound_of_eq237_sourceIndexMemIff",
        "CMP116Lemma3WeightedPostPSourceScaleBoundary.of_eq237",
        "CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
        "CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237",
    ]
    for target in live_field_targets:
        assert target in live_fields_md
    for row in live_field_rows:
        assert row in live_fields_md
    for target in stale_live_field_lines:
        assert f"\n{target}\n" not in live_fields_md
    assert "`cmp116Eq237Z0PrimeIndex_subset_global`" not in live_fields_md
    assert "  -> CMP116PostPResidualSourceBound\n" not in live_fields_md
    assert "  -> CMP116PostPResidualSourceMajorizationScaleFamily\n" not in live_fields_md

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md

    source_citations = json.loads(
        (ROOT / "docs" / "source-citations" / "cmp116-lemma3.json").read_text(
            encoding="utf-8"
        )
    )
    eq237_source_targets = {
        "cmp116.eq237.post-p-resummation": [
            "YangMills.RG.CMP116Eq237MajorizationBoundary",
            "YangMills.RG.cmp116Eq237Z0PrimeIndex",
            "YangMills.RG.cmp116Eq237Z0Fiber",
            "YangMills.RG.cmp116Eq237FixedZ0PrimeWeight",
            "YangMills.RG.cmp116Eq237Amplitude",
            "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
            "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
            "YangMills.RG.CMP116PostPResidualSourceBound",
        ],
        "cmp116.eq232.z0-gap-distance-geometric": [
            "YangMills.RG.CMP116Eq237MajorizationBoundary",
            "YangMills.RG.cmp116Eq237FixedZ0PrimeWeight",
            "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
            "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
        ],
        "cmp116.eq234.y0-subset-summation": [
            "YangMills.RG.CMP116Eq237MajorizationBoundary",
            "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
            "YangMills.RG.CMP116PostPResidualSourceBound",
            "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
        ],
        "cmp116.eq236.scale-transfer-geometric": [
            "YangMills.RG.CMP116Eq237MajorizationBoundary",
            "YangMills.RG.cmp116Eq237FixedZ0PrimeWeight",
            "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
            "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
        ],
        "cmp116.constants.c3-alpha5": [
            "YangMills.RG.CMP116Eq237MajorizationBoundary",
            "YangMills.RG.cmp116Eq237Amplitude",
            "YangMills.RG.cmp116Eq237FixedZ0PrimeWeight",
            "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
            "YangMills.RG.cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237",
            "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
        ],
    }
    stale_eq237_source_targets = [
        "CMP116Eq237MajorizationBoundary",
        "cmp116Eq237FixedZ0PrimeWeight",
        "cmp116Eq237Amplitude",
        "cmp116PostPResidualSourceBound_of_eq237",
        "CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
        "CMP116PostPResidualSourceBound",
    ]
    for source_key, expected_targets in eq237_source_targets.items():
        citation = next(
            citation
            for citation in source_citations["citations"]
            if citation["key"] == source_key
        )
        for target in expected_targets:
            assert target in citation["lean_targets"]
        for target in stale_eq237_source_targets:
            assert target not in citation["lean_targets"]

    for target in [
        "YangMills.RG.CMP116Eq237MajorizationBoundary",
        "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
    ]:
        assert any(
            item["citation_key"] == "cmp116.eq237.post-p-resummation"
            for item in lean_crosswalk["targets"][target]
        )
        assert (
            f"| `{target}` | `cmp116.eq237.post-p-resummation` |"
            in lean_crosswalk_md
        )
    for target in [
        "CMP116Eq237MajorizationBoundary",
        "cmp116PostPResidualSourceBound_of_eq237",
    ]:
        assert target not in lean_crosswalk["targets"]
        assert (
            f"| `{target}` | `cmp116.eq237.post-p-resummation` |"
            not in lean_crosswalk_md
        )


def test_hypothesis_queue_keeps_eq237_fixed_z0prime_open_gate() -> None:
    proof_key = "proof.eq237.fixed-z0prime-source-estimate"
    expected_live_hypotheses = [
        "fixed-Z0' Eq. (2.37) premise",
        "post-(2.37) final summation",
        "Z0/Z0' source dictionary",
    ]
    expected_source_keys = [
        "cmp116.eq237.post-p-resummation",
        "cmp116.constants.c3-alpha5",
        "crosswalk.eq237.combined-postp-route",
    ]
    expected_lean_targets = [
        "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
        "YangMills.RG.CMP116Eq237MajorizationBoundary",
        "YangMills.RG.cmp116Eq237FixedZ0PrimeWeight",
        "YangMills.RG.cmp116Eq237Amplitude",
    ]
    expected_next_action = (
        "Consume the named fixed-Z0' display and post-(2.37) final-summation premises "
        "by closing the D/P/Z0/Z0' dictionary, connected-component product dictionary, "
        "alpha5/C3 majorants, and half-exponent reserve; do not split off standalone "
        "normalized Z0 or Z0' theorems."
    )

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["rank"] == 5
    assert queued_card["live_hypotheses"] == expected_live_hypotheses
    assert queued_card["removes"] == [
        "caller-supplied combined CMP116PostPResidualSourceBound inputs"
    ]
    assert queued_card["source_keys"] == expected_source_keys
    assert queued_card["lean_targets"] == expected_lean_targets
    assert queued_card["next_action"] == expected_next_action

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    assert (
        f"| 5 | `{proof_key}` | fixed-Z0' Eq. (2.37) premise |"
        in hypothesis_queue_md
    )
    assert "`cmp116.eq237.post-p-resummation`" in hypothesis_queue_md
    assert "`YangMills.RG.cmp116Eq237FixedZ0PrimeWeight`" in hypothesis_queue_md


def test_eq237_proof_card_indices_record_source_display_dictionary_blocker() -> None:
    proof_key = "proof.eq237.fixed-z0prime-source-estimate"
    expected_status = "source_display_dictionary_blocker"

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["status"] == expected_status

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    assert f"## 5. `{proof_key}`" in proof_cards_md
    assert f"**Status:** `{expected_status}`" in proof_cards_md


def test_eq229_indices_keep_qualified_lean_targets() -> None:
    expected = [
        "YangMills.RG.CMP116Lemma3Eq229ScaleBoundary",
        "YangMills.RG.CMP116Eq229Summability",
        "YangMills.RG.cmp116H_termWeightSum_le_of_eq229",
        "YangMills.RG.cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound",
    ]
    proof_key = "proof.eq229.cammarota-dstage-summability"
    crosswalk_source_key = "crosswalk.eq229.cammarota-dstage-route"
    source_keys = [
        "cmp116.eq229.d-stage-summability",
        "cmp109.ref26.cammarota-infinite-range-cluster",
        "cammarota.cmp85.polymer-mayer-source-target",
        crosswalk_source_key,
    ]
    source_expected = [
        "YangMills.RG.CMP116Lemma3Eq229ScaleBoundary",
        "YangMills.RG.CMP116Eq229Summability",
        "YangMills.RG.cmp116H_termWeightSum_le_of_eq229",
    ]
    stale_source_targets = [
        "CMP116Lemma3Eq229ScaleBoundary",
        "CMP116Eq229Summability",
        "cmp116H_termWeightSum_le_of_eq229",
    ]

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    catalog_card = next(card for card in catalog["citations"] if card["key"] == proof_key)
    for target in expected:
        assert target in catalog_card["lean_targets"]

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["lean_targets"] == expected

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["lean_targets"] == expected

    router = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "source-key-router.json")
        .read_text(encoding="utf-8")
    )
    for source_key in source_keys:
        route = next(
            route
            for route in router["routes"][source_key]
            if route["proof_card"] == proof_key
        )
        assert route["lean_targets"] == expected

    expected_md_line = (
        "- Lean: `YangMills.RG.CMP116Lemma3Eq229ScaleBoundary`, "
        "`YangMills.RG.CMP116Eq229Summability`, "
        "`YangMills.RG.cmp116H_termWeightSum_le_of_eq229`, "
        "`YangMills.RG.cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound`"
    )
    source_router_md = (
        ROOT / "docs" / "source-db" / "indices" / "SOURCE-KEY-ROUTER.md"
    ).read_text(encoding="utf-8")
    assert expected_md_line in source_router_md

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"  - {target}" in proof_cards_md

    live_fields_md = (
        ROOT / "docs" / "source-db" / "indices" / "EQ229-CAMMAROTA-LIVE-FIELDS.md"
    ).read_text(encoding="utf-8")
    live_field_targets = [
        "YangMills.RG.CMP116Eq229Summability",
        "YangMills.RG.CMP116Lemma3Eq229ScaleBoundary",
        "YangMills.RG.cmp116Eq229Summability_of_product_majorant",
        "YangMills.RG.cmp116Eq229Summability_of_uniform_product_bound",
        "YangMills.RG.CammarotaCMP85Threshold.of_product_majorant",
        "YangMills.RG.CammarotaCMP85Threshold.of_uniform_product_bound",
        "YangMills.RG.CammarotaCMP85FiniteDStageSource",
        "YangMills.RG.CMP116Eq229Summability.of_cammarotaFiniteDStageSource",
        "YangMills.RG.CammarotaCMP85Threshold.of_finiteDStageSource",
    ]
    stale_live_field_lines = [
        "cmp116Eq229Summability_of_product_majorant",
        "cmp116Eq229Summability_of_uniform_product_bound",
        "CammarotaCMP85Threshold.of_product_majorant",
        "CammarotaCMP85Threshold.of_uniform_product_bound",
        "CammarotaCMP85FiniteDStageSource",
        "CMP116Eq229Summability.of_cammarotaFiniteDStageSource",
        "CammarotaCMP85Threshold.of_finiteDStageSource",
    ]
    for target in live_field_targets:
        assert target in live_fields_md
    for target in stale_live_field_lines:
        assert f"\n{target}\n" not in live_fields_md
    assert "feeds `CMP116Eq229Summability` only after dictionary work" not in live_fields_md
    assert "`CMP116Lemma3Eq229ScaleBoundary`" not in live_fields_md
    assert "derive `CMP116Eq229Summability` without assuming" not in live_fields_md

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md

    source_citations = json.loads(
        (ROOT / "docs" / "source-citations" / "cmp116-lemma3.json").read_text(
            encoding="utf-8"
        )
    )
    eq229_summability_source_keys = [
        "cmp116.eq229.d-stage-summability",
        "cmp109.ref26.cammarota-infinite-range-cluster",
        "cammarota.cmp85.polymer-mayer-source-target",
    ]
    for source_key in eq229_summability_source_keys:
        citation = next(
            citation
            for citation in source_citations["citations"]
            if citation["key"] == source_key
        )
        assert "YangMills.RG.CMP116Eq229Summability" in citation["lean_targets"]
        assert "CMP116Eq229Summability" not in citation["lean_targets"]

    source_catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "llm-operational-crosswalk.json")
        .read_text(encoding="utf-8")
    )
    source_entry = next(
        citation
        for citation in source_catalog["citations"]
        if citation["key"] == crosswalk_source_key
    )
    assert source_entry["lean_targets"] == source_expected
    for target in stale_source_targets:
        assert target not in source_entry["lean_targets"]

    lean_crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    for target in source_expected:
        assert target in lean_crosswalk["targets"]
        assert any(
            item["citation_key"] == crosswalk_source_key
            for item in lean_crosswalk["targets"][target]
        )
    for target in stale_source_targets:
        assert all(
            item["citation_key"] != crosswalk_source_key
            for item in lean_crosswalk["targets"].get(target, [])
        )

    lean_crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    for target in source_expected:
        assert f"| `{target}` | `{crosswalk_source_key}` |" in lean_crosswalk_md
    for target in stale_source_targets:
        assert f"| `{target}` | `{crosswalk_source_key}` |" not in lean_crosswalk_md


def test_hypothesis_queue_keeps_eq229_cammarota_open_gate() -> None:
    proof_key = "proof.eq229.cammarota-dstage-summability"
    expected_live_hypotheses = [
        "CMP116Lemma3Eq229ScaleBoundary",
        "CMP116Eq229Summability",
        "DIndex/DParts dictionary",
    ]
    expected_removes = [
        "manual Eq. (2.29) D-stage summability",
        "qualitative sufficiently-large/small source gap",
    ]
    expected_source_keys = [
        "cmp116.eq229.d-stage-summability",
        "cmp109.ref26.cammarota-infinite-range-cluster",
        "cammarota.cmp85.polymer-mayer-source-target",
        "crosswalk.eq229.cammarota-dstage-route",
    ]
    expected_lean_targets = [
        "YangMills.RG.CMP116Lemma3Eq229ScaleBoundary",
        "YangMills.RG.CMP116Eq229Summability",
        "YangMills.RG.cmp116H_termWeightSum_le_of_eq229",
        "YangMills.RG.cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound",
    ]
    expected_next_action = (
        "Obtain clean Cammarota CMP85 theorem text or PDF page; extract theorem, "
        "assumptions, constants, and route to Balaban Eq. (2.29)."
    )

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["rank"] == 4
    assert queued_card["live_hypotheses"] == expected_live_hypotheses
    assert queued_card["removes"] == expected_removes
    assert queued_card["source_keys"] == expected_source_keys
    assert queued_card["lean_targets"] == expected_lean_targets
    assert queued_card["next_action"] == expected_next_action

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    assert (
        f"| 4 | `{proof_key}` | CMP116Lemma3Eq229ScaleBoundary |"
        in hypothesis_queue_md
    )
    assert "`cammarota.cmp85.polymer-mayer-source-target`" in hypothesis_queue_md
    assert "`YangMills.RG.CMP116Eq229Summability`" in hypothesis_queue_md


def test_eq229_proof_card_indices_record_external_source_blocker_status() -> None:
    proof_key = "proof.eq229.cammarota-dstage-summability"
    expected_status = "blocked_on_external_source"

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["status"] == expected_status

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    assert f"## 4. `{proof_key}`" in proof_cards_md
    assert f"**Status:** `{expected_status}`" in proof_cards_md


def test_activity_termwise_indices_keep_qualified_lean_targets() -> None:
    expected = [
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary",
        "YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_resummation",
        "YangMills.RG.PhysicalGaugeLocalActivity.globalEval",
    ]
    proof_key = "proof.activity.termwise-identification"
    source_keys = [
        "cmp116.localized-activity.2.7-2.10",
        "cmp116.lemma3.window.2.14-2.38",
        "crosswalk.gaussian-root-activity-route",
    ]

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    catalog_card = next(card for card in catalog["citations"] if card["key"] == proof_key)
    for target in expected:
        assert target in catalog_card["lean_targets"]

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["lean_targets"] == expected

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["lean_targets"] == expected

    router = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "source-key-router.json")
        .read_text(encoding="utf-8")
    )
    for source_key in source_keys:
        route = next(
            route
            for route in router["routes"][source_key]
            if route["proof_card"] == proof_key
        )
        assert route["lean_targets"] == expected

    expected_md_line = (
        "- Lean: `YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary`, "
        "`YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_resummation`, "
        "`YangMills.RG.PhysicalGaugeLocalActivity.globalEval`"
    )
    source_router_md = (
        ROOT / "docs" / "source-db" / "indices" / "SOURCE-KEY-ROUTER.md"
    ).read_text(encoding="utf-8")
    assert expected_md_line in source_router_md

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"  - {target}" in proof_cards_md

    live_fields_md = (
        ROOT / "docs" / "source-db" / "indices" / "ACTIVITY-TERMWISE-LIVE-FIELDS.md"
    ).read_text(encoding="utf-8")
    live_field_targets = [
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification",
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate",
        "YangMills.RG.PhysicalGaugeLocalActivity.globalEval",
    ]
    stale_live_field_targets = [
        "CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification",
        "CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate",
        "PhysicalGaugeLocalActivity.globalEval",
    ]
    for target in live_field_targets:
        assert f"`{target}`" in live_fields_md
    for target in stale_live_field_targets:
        assert f"`{target}`" not in live_fields_md
    assert "before `termwise_estimate` can be theorem-fed" not in live_fields_md

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md

    source_citations = json.loads(
        (ROOT / "docs" / "source-citations" / "cmp116-lemma3.json").read_text(
            encoding="utf-8"
        )
    )
    localized_activity = next(
        citation
        for citation in source_citations["citations"]
        if citation["key"] == "cmp116.localized-activity.2.7-2.10"
    )
    assert (
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary"
        in localized_activity["lean_targets"]
    )
    assert (
        "YangMills.RG.PhysicalGaugeLocalActivity.globalEval"
        in localized_activity["lean_targets"]
    )
    assert "CMP116Lemma3ActivityTermwiseScaleBoundary" not in localized_activity["lean_targets"]
    assert "PhysicalGaugeLocalActivity.globalEval" not in localized_activity["lean_targets"]

    lemma3_window = next(
        citation
        for citation in source_citations["citations"]
        if citation["key"] == "cmp116.lemma3.window.2.14-2.38"
    )
    assert (
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary"
        in lemma3_window["lean_targets"]
    )


def test_activity_live_fields_keep_qualified_lean_targets() -> None:
    live_field_key = "proof.activity.termwise.live-fields.v2"
    local_activity_key = "proof.local-activity.construction.v2"
    raw_termwise_key = "proof.raw-pointwise-decay.termwise.v2"
    live_field_expected = [
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification",
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate",
        "YangMills.RG.PhysicalGaugeLocalActivity.globalEval",
        "YangMills.RG.BalabanCMP116SourceAssumptions.local_physical_activity_construction",
        "YangMills.RG.BalabanCMP116SourceAssumptions.raw_pointwise_decay",
    ]
    raw_termwise_expected = [
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate",
        "YangMills.RG.BalabanCMP116SourceAssumptions.raw_pointwise_decay",
        "YangMills.RG.CMP116Lemma3ActivityEstimateScaleFamily",
    ]
    stale_targets = [
        "CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification",
        "CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate",
        "PhysicalGaugeLocalActivity.globalEval",
        "BalabanCMP116SourceAssumptions.local_physical_activity_construction",
        "BalabanCMP116SourceAssumptions.raw_pointwise_decay",
        "CMP116Lemma3ActivityEstimateScaleFamily",
        "cmp116.localized-activity.2.7-2.10",
    ]

    catalog = json.loads(
        (
            ROOT
            / "docs"
            / "source-db"
            / "catalogs"
            / "gaussian-root-hessian-live-fields.json"
        ).read_text(encoding="utf-8")
    )
    entries = {entry["key"]: entry for entry in catalog["citations"]}

    assert entries[live_field_key]["lean_targets"] == live_field_expected
    assert entries[local_activity_key]["lean_targets"] == [
        "YangMills.RG.BalabanCMP116SourceAssumptions.local_physical_activity_construction",
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification",
        "YangMills.RG.PhysicalGaugeLocalActivity.globalEval",
    ]
    assert entries[raw_termwise_key]["lean_targets"] == raw_termwise_expected
    assert {
        link["lean_symbol"]
        for link in entries[live_field_key]["dictionary_links"]
    } == {
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification",
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate",
        "YangMills.RG.BalabanCMP116SourceAssumptions.raw_pointwise_decay",
    }
    for key in [live_field_key, local_activity_key, raw_termwise_key]:
        for stale in stale_targets:
            assert stale not in entries[key]["lean_targets"]
    assert {
        (link["source_symbol"], link["lean_symbol"], link["status"])
        for link in entries[local_activity_key]["dictionary_links"]
    } == {
        (
            "cmp116.localized-activity.2.7-2.10",
            "YangMills.RG.BalabanCMP116SourceAssumptions.local_physical_activity_construction",
            "dictionary_open",
        )
    }

def test_hypothesis_queue_keeps_activity_termwise_open_gate() -> None:
    proof_key = "proof.activity.termwise-identification"
    expected_live_hypotheses = [
        "CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification",
        "CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate",
    ]
    expected_removes = [
        "manual hglobal activity identification",
        "manual hterm termwise norm estimate",
    ]
    expected_source_keys = [
        "cmp116.localized-activity.2.7-2.10",
        "cmp116.lemma3.window.2.14-2.38",
        "crosswalk.gaussian-root-activity-route",
    ]
    expected_lean_targets = [
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary",
        "YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_resummation",
        "YangMills.RG.PhysicalGaugeLocalActivity.globalEval",
    ]
    expected_next_action = (
        "Extract H(Z) finite-sum dictionary around CMP116 (2.7)-(2.14), "
        "then feed termwise estimates around (2.14)-(2.38)."
    )

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["rank"] == 6
    assert queued_card["live_hypotheses"] == expected_live_hypotheses
    assert queued_card["removes"] == expected_removes
    assert queued_card["source_keys"] == expected_source_keys
    assert queued_card["lean_targets"] == expected_lean_targets
    assert queued_card["next_action"] == expected_next_action

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    assert (
        f"| 6 | `{proof_key}` | "
        "CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification |"
        in hypothesis_queue_md
    )
    assert "`cmp116.localized-activity.2.7-2.10`" in hypothesis_queue_md
    assert "`YangMills.RG.PhysicalGaugeLocalActivity.globalEval`" in hypothesis_queue_md


def test_activity_termwise_proof_card_indices_record_dictionary_blocker_status() -> None:
    proof_key = "proof.activity.termwise-identification"
    expected_status = "source_to_lean_dictionary_blocker"

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["status"] == expected_status

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    assert f"## 6. `{proof_key}`" in proof_cards_md
    assert f"**Status:** `{expected_status}`" in proof_cards_md


def test_appendixf_hsharp_indices_keep_qualified_lean_targets() -> None:
    expected = [
        "YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound",
        "YangMills.RG.balabanCMP116AppendixFHsharpOfIntegratedKsharp",
        "YangMills.RG.appendixFHoleExpWeight",
    ]
    proof_key = "proof.dimock.appendixf.hsharp-feed"
    source_keys = [
        "crosswalk.dimock.appendixf-hole-cluster-route",
        "dimockii.appendix-f.cluster-with-holes",
        "dimockii.appendix-f.second-ursell.645-646",
    ]

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    catalog_card = next(card for card in catalog["citations"] if card["key"] == proof_key)
    assert catalog_card["lean_targets"] == expected

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["lean_targets"] == expected

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["lean_targets"] == expected

    router = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "source-key-router.json")
        .read_text(encoding="utf-8")
    )
    for source_key in source_keys:
        route = next(
            route
            for route in router["routes"][source_key]
            if route["proof_card"] == proof_key
        )
        assert route["lean_targets"] == expected

    expected_md_line = (
        "- Lean: `YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound`, "
        "`YangMills.RG.balabanCMP116AppendixFHsharpOfIntegratedKsharp`, "
        "`YangMills.RG.appendixFHoleExpWeight`"
    )
    source_router_md = (
        ROOT / "docs" / "source-db" / "indices" / "SOURCE-KEY-ROUTER.md"
    ).read_text(encoding="utf-8")
    assert expected_md_line in source_router_md

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"  - {target}" in proof_cards_md

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md


def test_dimock_appendixf_crosswalk_keeps_qualified_lean_targets() -> None:
    source_key = "crosswalk.dimock.appendixf-hole-cluster-route"
    expected = [
        "YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp",
        "YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound",
        "YangMills.RG.AppendixFHsharpLeafSource",
    ]
    stale = [
        "omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp",
        "omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound",
        "AppendixFHsharpLeafSource",
    ]

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "llm-operational-crosswalk.json")
        .read_text(encoding="utf-8")
    )
    citation = next(item for item in catalog["citations"] if item["key"] == source_key)
    assert citation["lean_targets"] == expected

    crosswalk = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json")
        .read_text(encoding="utf-8")
    )["targets"]
    for target in expected:
        assert any(row["citation_key"] == source_key for row in crosswalk[target])
    for target in stale:
        assert not any(
            row["citation_key"] == source_key for row in crosswalk.get(target, [])
        )

    crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"| `{target}` | `{source_key}` |" in crosswalk_md
    for target in stale:
        assert f"| `{target}` | `{source_key}` |" not in crosswalk_md


def test_dimock_extracted_appendixf_targets_keep_qualified_lean_routes() -> None:
    target_pairs = {
        "dimocki.lemma25.polymer-summability.289-290": [
            (
                "appendixFHoleRootSumConstant",
                "YangMills.RG.appendixFHoleRootSumConstant",
            ),
        ],
        "dimocki.polymer-summability.corollary26.292-295": [
            (
                "appendixFHoleRootSumConstant",
                "YangMills.RG.appendixFHoleRootSumConstant",
            ),
            (
                "appendixFSecondUrsellLeafConstant",
                "YangMills.RG.appendixFSecondUrsellLeafConstant",
            ),
            (
                "omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound",
                "YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound",
            ),
        ],
        "dimockii.appendix-f.metric-first-activity.637-644": [
            (
                "appendixFHoleCoverUnion_discreteModifiedMetric_add_one_le_sum",
                "YangMills.RG.appendixFHoleCoverUnion_discreteModifiedMetric_add_one_le_sum",
            ),
            (
                "appendixFHoleTargetFiber_discreteModifiedMetric_add_one_le_sum",
                "YangMills.RG.appendixFHoleTargetFiber_discreteModifiedMetric_add_one_le_sum",
            ),
        ],
        "dimockii.appendix-f.second-ursell.645-646": [
            (
                "appendixFSecondUrsellLeafConstant",
                "YangMills.RG.appendixFSecondUrsellLeafConstant",
            ),
            (
                "appendixFSecondUrsellMomentConstant",
                "YangMills.RG.appendixFSecondUrsellMomentConstant",
            ),
        ],
        "dimockii.lemmaE.3.modified-metric-summability.627-632": [
            (
                "appendixFHoleRootSumConstant",
                "YangMills.RG.appendixFHoleRootSumConstant",
            ),
            (
                "omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound",
                "YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound",
            ),
        ],
    }

    catalog = json.loads(
        (
            ROOT / "docs" / "source-db" / "catalogs" / "dimock-rg-i-iii-extracted.json"
        ).read_text(encoding="utf-8")
    )
    citations = {item["key"]: item for item in catalog["citations"]}

    crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )["targets"]
    crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")

    for source_key, pairs in target_pairs.items():
        catalog_targets = citations[source_key]["lean_targets"]
        for stale, qualified in pairs:
            assert qualified in catalog_targets
            assert stale not in catalog_targets
            assert any(
                item["citation_key"] == source_key
                for item in crosswalk.get(qualified, [])
            )
            assert not any(
                item["citation_key"] == source_key
                for item in crosswalk.get(stale, [])
            )
            assert f"| `{qualified}` | `{source_key}` |" in crosswalk_md
            assert f"| `{stale}` | `{source_key}` |" not in crosswalk_md


def test_hypothesis_queue_keeps_appendixf_hsharp_open_gate() -> None:
    proof_key = "proof.dimock.appendixf.hsharp-feed"
    expected_live_hypotheses = [
        "activity bound |H(X)| <= H0 exp(-kappa d_M)",
        "H0 <= c0",
        "kappa >= 3*kappa0+3",
        "modified metric summability",
    ]
    expected_source_keys = [
        "crosswalk.dimock.appendixf-hole-cluster-route",
        "dimockii.appendix-f.cluster-with-holes",
        "dimockii.appendix-f.second-ursell.645-646",
    ]
    expected_lean_targets = [
        "YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound",
        "YangMills.RG.balabanCMP116AppendixFHsharpOfIntegratedKsharp",
        "YangMills.RG.appendixFHoleExpWeight",
    ]
    expected_next_action = (
        "Use Batch 001 Dimock extraction as stable; focus on feeding the "
        "activity bound from CMP116/Balaban."
    )

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["rank"] == 8
    assert queued_card["live_hypotheses"] == expected_live_hypotheses
    assert queued_card["removes"] == [
        "manual cluster-with-holes package once activity estimate is supplied"
    ]
    assert queued_card["source_keys"] == expected_source_keys
    assert queued_card["lean_targets"] == expected_lean_targets
    assert queued_card["next_action"] == expected_next_action

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    assert f"| 8 | `{proof_key}` | activity bound |H(X)| <= H0 exp(-kappa d_M) |" in (
        hypothesis_queue_md
    )
    assert "`dimockii.appendix-f.second-ursell.645-646`" in hypothesis_queue_md
    assert (
        "`YangMills.RG.balabanCMP116AppendixFHsharpOfIntegratedKsharp`"
        in hypothesis_queue_md
    )


def test_appendixf_hsharp_proof_card_indices_record_partial_extraction_status() -> None:
    proof_key = "proof.dimock.appendixf.hsharp-feed"
    expected_status = "partially_source_extracted"

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["status"] == expected_status

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    assert f"## 8. `{proof_key}`" in proof_cards_md
    assert f"**Status:** `{expected_status}`" in proof_cards_md


def test_flow_ir_indices_keep_qualified_lean_targets() -> None:
    expected = [
        "YangMills.RG.logistic_geometric_decay",
        "YangMills.RG.remainder_geometric_of_logistic",
        "YangMills.RG.BalabanCMP116SourceAssumptions.coupling_recursion",
        "YangMills.RG.BalabanCMP116SourceAssumptions.ir_bound",
    ]
    proof_key = "proof.flow.ir.bridge"
    source_key = "crosswalk.flow-ir-asymptotic-freedom-route"
    source_expected = [
        "YangMills.RG.logistic_geometric_decay",
        "YangMills.RG.remainder_geometric_of_logistic",
        "YangMills.RG.BalabanCMP116SourceAssumptions.ir_bound",
    ]
    consumer_live_field_targets = [
        "YangMills.RG.lattice_mass_gap_of_singleScaleUVDecay_marginal",
        "YangMills.RG.marginal_coupling_remainder_tsum_le_of_recursion",
    ]

    source_catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "llm-operational-crosswalk.json")
        .read_text(encoding="utf-8")
    )
    source_entry = next(
        citation for citation in source_catalog["citations"] if citation["key"] == source_key
    )
    assert source_entry["lean_targets"] == source_expected
    assert "RG.CouplingFlow.logistic_geometric_decay" not in source_entry["lean_targets"]
    assert "remainder_geometric_of_logistic" not in source_entry["lean_targets"]
    assert "ir_bound" not in source_entry["lean_targets"]

    lean_crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    for target in source_expected:
        assert target in lean_crosswalk["targets"]
    assert "RG.CouplingFlow.logistic_geometric_decay" not in lean_crosswalk["targets"]
    assert "remainder_geometric_of_logistic" not in lean_crosswalk["targets"]
    assert "ir_bound" not in lean_crosswalk["targets"]

    lean_crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    for target in source_expected:
        assert f"`{target}`" in lean_crosswalk_md
    assert "| `RG.CouplingFlow.logistic_geometric_decay` |" not in lean_crosswalk_md
    assert "| `remainder_geometric_of_logistic` |" not in lean_crosswalk_md
    assert "| `ir_bound` |" not in lean_crosswalk_md

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    catalog_card = next(card for card in catalog["citations"] if card["key"] == proof_key)
    for target in expected:
        assert target in catalog_card["lean_targets"]

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["lean_targets"] == expected

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["lean_targets"] == expected

    router = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "source-key-router.json")
        .read_text(encoding="utf-8")
    )
    route = next(
        route
        for route in router["routes"][source_key]
        if route["proof_card"] == proof_key
    )
    assert route["lean_targets"] == expected

    expected_md_line = (
        "- Lean: `YangMills.RG.logistic_geometric_decay`, "
        "`YangMills.RG.remainder_geometric_of_logistic`, "
        "`YangMills.RG.BalabanCMP116SourceAssumptions.coupling_recursion`, "
        "`YangMills.RG.BalabanCMP116SourceAssumptions.ir_bound`"
    )
    source_router_md = (
        ROOT / "docs" / "source-db" / "indices" / "SOURCE-KEY-ROUTER.md"
    ).read_text(encoding="utf-8")
    assert expected_md_line in source_router_md

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"  - {target}" in proof_cards_md

    live_fields_md = (
        ROOT / "docs" / "source-db" / "indices" / "FLOW-IR-LIVE-FIELDS.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"`{target}`" in live_fields_md
    for target in consumer_live_field_targets:
        assert f"`{target}`" in live_fields_md
    assert (
        "| scale dictionary | source scale, block, and metric conventions linking "
        "CMP109/CMP119 to repository indices | flow/IR consumers in "
        "`YangMills.RG.BalabanCMP116SourceAssumptions` |"
    ) not in live_fields_md
    assert "`BalabanCMP116SourceAssumptions.coupling_recursion`" not in live_fields_md
    assert "`CouplingFlow.logistic_geometric_decay`" not in live_fields_md
    assert "`remainder_geometric_of_logistic`" not in live_fields_md
    assert "`BalabanCMP116SourceAssumptions.ir_bound`" not in live_fields_md

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    assert "`YangMills.RG.logistic_geometric_decay`" in hypothesis_queue_md
    assert (
        "`YangMills.RG.BalabanCMP116SourceAssumptions.coupling_recursion`"
        in hypothesis_queue_md
    )


def test_hypothesis_queue_keeps_flow_ir_open_gate() -> None:
    proof_key = "proof.flow.ir.bridge"
    expected_live_hypotheses = [
        "coupling flow assumptions",
        "ir_bound",
        "geometric contraction of irrelevant operators",
    ]
    expected_source_keys = [
        "crosswalk.flow-ir-asymptotic-freedom-route",
    ]
    expected_lean_targets = [
        "YangMills.RG.logistic_geometric_decay",
        "YangMills.RG.remainder_geometric_of_logistic",
        "YangMills.RG.BalabanCMP116SourceAssumptions.coupling_recursion",
        "YangMills.RG.BalabanCMP116SourceAssumptions.ir_bound",
    ]
    expected_next_action = (
        "Catalog exact beta-flow formulas and separate them from the "
        "already-formal irrelevant logistic surrogate."
    )

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["rank"] == 10
    assert queued_card["live_hypotheses"] == expected_live_hypotheses
    assert queued_card["removes"] == [
        "misuse of g_k <= C*r^k for 4D marginal gauge coupling"
    ]
    assert queued_card["source_keys"] == expected_source_keys
    assert queued_card["lean_targets"] == expected_lean_targets
    assert queued_card["next_action"] == expected_next_action

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    assert f"| 10 | `{proof_key}` | coupling flow assumptions |" in (
        hypothesis_queue_md
    )
    assert "`crosswalk.flow-ir-asymptotic-freedom-route`" in hypothesis_queue_md
    assert "`YangMills.RG.BalabanCMP116SourceAssumptions.ir_bound`" in hypothesis_queue_md


def test_flow_ir_proof_card_indices_record_conceptual_blocker_status() -> None:
    proof_key = "proof.flow.ir.bridge"
    expected_status = "conceptual_bridge_blocker"

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["status"] == expected_status

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    assert f"## 10. `{proof_key}`" in proof_cards_md
    assert f"**Status:** `{expected_status}`" in proof_cards_md


def test_gaussian_root_indices_keep_qualified_lean_targets() -> None:
    expected = [
        "YangMills.RG.PhysicalLocalizedCovarianceRootCertificate",
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward",
        "YangMills.RG.balabanCMP116Dmu0",
    ]
    crosswalk_source_key = "crosswalk.gaussian-root-activity-route"
    crosswalk_expected = [
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward",
        "YangMills.RG.PhysicalLocalizedCovarianceRootCertificate",
        "YangMills.RG.BalabanCMP116SourceAssumptions.rawSource",
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary",
    ]
    stale_crosswalk_targets = [
        "PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward",
        "PhysicalLocalizedCovarianceRootCertificate",
        "BalabanCMP116SourceAssumptions.rawSource",
        "CMP116Lemma3ActivityTermwiseScaleBoundary",
    ]
    proof_key = "proof.gaussian.root.localization-certificate"
    source_keys = [
        "cmp116.gaussian-pushforward.2.5-2.6",
        "cmp116.localized-activity.2.7-2.10",
        "cmp95.covariance-green.bounds-source-target",
        "cmp96.one-step-covariance-law-source-target",
    ]

    catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    catalog_card = next(card for card in catalog["citations"] if card["key"] == proof_key)
    for target in expected:
        assert target in catalog_card["lean_targets"]

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["lean_targets"] == expected

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["lean_targets"] == expected

    router = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "source-key-router.json")
        .read_text(encoding="utf-8")
    )
    for source_key in source_keys:
        route = next(
            route
            for route in router["routes"][source_key]
            if route["proof_card"] == proof_key
        )
        assert route["lean_targets"] == expected

    expected_md_line = (
        "- Lean: `YangMills.RG.PhysicalLocalizedCovarianceRootCertificate`, "
        "`YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward`, "
        "`YangMills.RG.balabanCMP116Dmu0`"
    )
    source_router_md = (
        ROOT / "docs" / "source-db" / "indices" / "SOURCE-KEY-ROUTER.md"
    ).read_text(encoding="utf-8")
    assert expected_md_line in source_router_md

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"  - {target}" in proof_cards_md

    live_fields_md = (
        ROOT / "docs" / "source-db" / "indices" / "GAUSSIAN-ROOT-HESSIAN-LIVE-FIELDS.md"
    ).read_text(encoding="utf-8")
    live_field_targets = [
        (
            "`YangMills.RG.PhysicalLocalizedCovarianceRootCertificate`; "
            "`YangMills.RG.BalabanCMP116SourceAssumptions.covariance_root_certificate`"
        ),
        (
            "`YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses."
            "gaussian_pushforward`; "
            "`YangMills.RG.BalabanCMP116SourceAssumptions.gaussian_pushforward`"
        ),
        (
            "`YangMills.RG.BalabanCMP116SourceAssumptions.root_localization`; "
            "`YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses."
            "root_localization`"
        ),
    ]
    stale_live_field_rows = [
        (
            "| covariance/root certificate | CMP116 covariance/root definitions + "
            "Dimock-style architecture as guide | `PhysicalLocalizedCovarianceRootCertificate` |"
        ),
        (
            "| gaussian pushforward | CMP116 (2.5)-(2.6) + coordinate/Jacobian "
            "dictionary | `gaussian_pushforward` |"
        ),
        (
            "| root localization | CMP116 (2.7)-(2.10), covariance-root localization | "
            "`root_localization` |"
        ),
    ]
    for target in live_field_targets:
        assert target in live_fields_md
    for row in stale_live_field_rows:
        assert row not in live_fields_md

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for source_key in source_keys:
        assert f"`{source_key}`" in hypothesis_queue_md
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md

    source_citations = json.loads(
        (ROOT / "docs" / "source-citations" / "cmp116-lemma3.json").read_text(
            encoding="utf-8"
        )
    )
    gaussian_pushforward = next(
        citation
        for citation in source_citations["citations"]
        if citation["key"] == "cmp116.gaussian-pushforward.2.5-2.6"
    )
    assert "YangMills.RG.balabanCMP116Dmu0" in gaussian_pushforward["lean_targets"]
    assert "balabanCMP116Dmu0" not in gaussian_pushforward["lean_targets"]

    lean_crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    assert "YangMills.RG.balabanCMP116Dmu0" in lean_crosswalk["targets"]
    assert "balabanCMP116Dmu0" not in lean_crosswalk["targets"]

    lean_crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    assert "`YangMills.RG.balabanCMP116Dmu0`" in lean_crosswalk_md
    assert "| `balabanCMP116Dmu0` |" not in lean_crosswalk_md

    crosswalk_catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "llm-operational-crosswalk.json")
        .read_text(encoding="utf-8")
    )
    crosswalk_entry = next(
        citation
        for citation in crosswalk_catalog["citations"]
        if citation["key"] == crosswalk_source_key
    )
    assert crosswalk_entry["lean_targets"] == crosswalk_expected
    for target in stale_crosswalk_targets:
        assert target not in crosswalk_entry["lean_targets"]

    for target in crosswalk_expected:
        assert target in lean_crosswalk["targets"]
        assert any(
            item["citation_key"] == crosswalk_source_key
            for item in lean_crosswalk["targets"][target]
        )
        assert f"| `{target}` | `{crosswalk_source_key}` |" in lean_crosswalk_md
    for target in stale_crosswalk_targets:
        assert all(
            item["citation_key"] != crosswalk_source_key
            for item in lean_crosswalk["targets"].get(target, [])
        )
        assert f"| `{target}` | `{crosswalk_source_key}` |" not in lean_crosswalk_md


def test_hypothesis_queue_keeps_gaussian_root_open_gate() -> None:
    proof_key = "proof.gaussian.root.localization-certificate"
    expected_live_hypotheses = [
        "gaussian_pushforward",
        "root_localization",
        "PhysicalLocalizedCovarianceRootCertificate",
    ]
    expected_source_keys = [
        "cmp116.gaussian-pushforward.2.5-2.6",
        "cmp116.localized-activity.2.7-2.10",
        "cmp95.covariance-green.bounds-source-target",
        "cmp96.one-step-covariance-law-source-target",
    ]
    expected_lean_targets = [
        "YangMills.RG.PhysicalLocalizedCovarianceRootCertificate",
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward",
        "YangMills.RG.balabanCMP116Dmu0",
    ]
    expected_next_action = (
        "Create CMP95/CMP96 structured catalogs, then link root localization "
        "to CMP116 activity construction."
    )

    hypothesis_queue = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "hypothesis-removal-queue.json")
        .read_text(encoding="utf-8")
    )
    queued_card = next(card for card in hypothesis_queue["queue"] if card["key"] == proof_key)
    assert queued_card["rank"] == 7
    assert queued_card["live_hypotheses"] == expected_live_hypotheses
    assert queued_card["removes"] == ["manual Gaussian/root/source package fields"]
    assert queued_card["source_keys"] == expected_source_keys
    assert queued_card["lean_targets"] == expected_lean_targets
    assert queued_card["next_action"] == expected_next_action

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    assert f"| 7 | `{proof_key}` | gaussian_pushforward |" in hypothesis_queue_md
    assert "`cmp96.one-step-covariance-law-source-target`" in hypothesis_queue_md
    assert "`YangMills.RG.PhysicalLocalizedCovarianceRootCertificate`" in hypothesis_queue_md


def test_gaussian_root_proof_card_indices_record_dictionary_blocker_status() -> None:
    proof_key = "proof.gaussian.root.localization-certificate"
    expected_status = "source_to_lean_dictionary_blocker"

    card_index = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "proof-obligation-cards.json")
        .read_text(encoding="utf-8")
    )
    indexed_card = next(card for card in card_index["cards"] if card["key"] == proof_key)
    assert indexed_card["status"] == expected_status

    proof_cards_md = (
        ROOT / "docs" / "source-db" / "indices" / "PROOF-OBLIGATION-CARDS.md"
    ).read_text(encoding="utf-8")
    assert f"## 7. `{proof_key}`" in proof_cards_md
    assert f"**Status:** `{expected_status}`" in proof_cards_md


def test_gaussian_root_live_fields_route_source_anchors_outside_lean_targets() -> None:
    live_fields = json.loads(
        (
            ROOT
            / "docs"
            / "source-db"
            / "catalogs"
            / "gaussian-root-hessian-live-fields.json"
        ).read_text(encoding="utf-8")
    )
    cards = {card["key"]: card for card in live_fields["citations"]}
    covroot_card = cards["proof.gaussian.covariance-root-certificate.v2"]
    root_card = cards["proof.root.localization.v2"]
    stale_source_targets = {
        "cmp116.gaussian-pushforward.2.5-2.6",
        "dimockii.fluctuation-covariance.271-276",
        "cmp116.localized-activity.2.7-2.10",
    }

    for card in (covroot_card, root_card):
        assert not (set(card["lean_targets"]) & stale_source_targets)

    covroot_links = {
        (link["source_symbol"], link["lean_symbol"], link["status"])
        for link in covroot_card["dictionary_links"]
        if link["id"]
        in {
            "covroot.cmp116-pushforward-anchor",
            "covroot.dimockii-architecture-reference",
        }
    }
    assert covroot_links == {
        (
            "cmp116.gaussian-pushforward.2.5-2.6",
            "YangMills.RG.PhysicalLocalizedCovarianceRootCertificate",
            "dictionary_open",
        ),
        (
            "dimockii.fluctuation-covariance.271-276",
            "YangMills.RG.PhysicalLocalizedCovarianceRootCertificate",
            "operational",
        ),
    }

    root_links = {
        (link["source_symbol"], link["lean_symbol"], link["status"])
        for link in root_card["dictionary_links"]
        if link["id"] == "root.localization.localized-activity-anchor"
    }
    assert root_links == {
        (
            "cmp116.localized-activity.2.7-2.10",
            "YangMills.RG.BalabanCMP116SourceAssumptions.root_localization",
            "dictionary_open",
        )
    }


def test_wilson_hessian_routes_keep_qualified_lean_targets() -> None:
    cmp99_expected = [
        "YangMills.RG.PhysicalLocalizedCovarianceRootCertificate",
        "YangMills.RG.physicalGaugeWilsonHessianIdentification",
        "YangMills.RG.BalabanCMP116SourceAssumptions.covariance_root_certificate",
    ]
    cmp102_expected = [
        "YangMills.RG.physicalGaugeWilsonHessianIdentification",
        "YangMills.RG.BalabanCMP116SourceAssumptions.wilson_hessian_identification",
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.wilson_hessian_identification",
    ]
    proof_key = "proof.gaussian.root.localization-certificate"

    live_fields = json.loads(
        (
            ROOT
            / "docs"
            / "source-db"
            / "catalogs"
            / "gaussian-root-hessian-live-fields.json"
        ).read_text(encoding="utf-8")
    )
    wilson_card = next(
        card
        for card in live_fields["citations"]
        if card["key"] == "proof.wilson.hessian.identification.v2"
    )
    for target in cmp102_expected[1:]:
        assert target in wilson_card["lean_targets"]
    assert "YangMills.RG.PhysicalGaugeCMP116Dictionary" in wilson_card["lean_targets"]

    spine = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "spine-backlog.json")
        .read_text(encoding="utf-8")
    )
    cmp99 = next(
        card
        for card in spine["citations"]
        if card["key"] == "cmp99.background-field-propagator-source-target"
    )
    assert cmp99["lean_targets"] == cmp99_expected
    cmp102 = next(
        card
        for card in spine["citations"]
        if card["key"] == "cmp102.variational-hessian-expansion-source-target"
    )
    assert cmp102["lean_targets"] == cmp102_expected

    router = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "source-key-router.json")
        .read_text(encoding="utf-8")
    )
    cmp99_route = next(
        route
        for route in router["routes"]["cmp99.background-field-propagator-source-target"]
        if route["proof_card"] == proof_key
    )
    assert cmp99_route["lean_targets"] == cmp99_expected
    cmp102_route = next(
        route
        for route in router["routes"]["cmp102.variational-hessian-expansion-source-target"]
        if route["proof_card"] == proof_key
    )
    assert cmp102_route["lean_targets"] == cmp102_expected

    source_router_md = (
        ROOT / "docs" / "source-db" / "indices" / "SOURCE-KEY-ROUTER.md"
    ).read_text(encoding="utf-8")
    assert (
        "- Lean: `YangMills.RG.PhysicalLocalizedCovarianceRootCertificate`, "
        "`YangMills.RG.physicalGaugeWilsonHessianIdentification`, "
        "`YangMills.RG.BalabanCMP116SourceAssumptions.covariance_root_certificate`"
    ) in source_router_md
    assert (
        "- Lean: `YangMills.RG.physicalGaugeWilsonHessianIdentification`, "
        "`YangMills.RG.BalabanCMP116SourceAssumptions.wilson_hessian_identification`, "
        "`YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.wilson_hessian_identification`"
    ) in source_router_md

    gaussian_root_hessian_md = (
        ROOT
        / "docs"
        / "source-db"
        / "indices"
        / "GAUSSIAN-ROOT-HESSIAN-LIVE-FIELDS.md"
    ).read_text(encoding="utf-8")
    assert "YangMills.RG.physicalGaugeWilsonHessianIdentification" in gaussian_root_hessian_md
    assert (
        "YangMills.RG.BalabanCMP116SourceAssumptions.wilson_hessian_identification"
        in gaussian_root_hessian_md
    )


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


def test_lean_lookup_finds_eq231_y0cstar_gap_source_lock(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("CMP116Eq231Y0cStarInteriorBoundaryToGapSource", path=output)
    captured = capsys.readouterr()
    assert "proof.eq231.endpoint-base-dictionary.source-audit [lean_linked]" in captured.out
    assert "proof.eq231.field.bond-fst-mem-gapCubes [lean_linked]" in captured.out
    assert "dictionary link: source_sentence_needed/pending" in captured.out
    assert "Need b=(b_-,b_+) -> encoded bond=(b_-,direction)" in captured.out
    assert "primary-source sentence identifying the CMP109 positive tail/base endpoint" in captured.out
    assert "no Lean target matches" not in captured.out


def test_search_finds_eq231_no_more_routing_guard(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("no more eq231 routing", path=output)
    captured = capsys.readouterr()
    assert "guard.no-more-eq231-routing [lean_linked]" in captured.out
    assert "new work must remove a live source hypothesis" in captured.out


def test_eq231_crosswalk_route_keeps_qualified_lean_targets() -> None:
    source_key = "crosswalk.eq231.p-family-source-dictionary-route"
    expected = [
        "YangMills.RG.cmp116Eq231GapCarrier",
        "YangMills.RG.cmp116Eq231GapMass",
        "YangMills.RG.cmp116Eq231GapCarrier_card_eq_four_scale4_gapMass",
        "YangMills.RG.cmp116Eq231GapCarrier_card_le_four_scale4_gapMass",
        "YangMills.RG.cmp116Eq231SourcePIndex_mem_iff",
        "YangMills.RG.cmp116Eq231PIndex_eq_sourceFilteredBondSets_of_mem_iff",
        "YangMills.RG.CMP116Eq231PBondBoundary.of_balabanPFamilySourcePackage",
        (
            "YangMills.RG."
            "CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets"
        ),
        (
            "YangMills.RG."
            "CMP116Lemma3WeightedPostPScaleSourceAssumptions."
            "of_eq231_filteredBondSets"
        ),
    ]
    stale = [
        "cmp116Eq231GapCarrier",
        "cmp116Eq231GapMass",
        "cmp116Eq231GapCarrier_card_eq_four_scale4_gapMass",
        "cmp116Eq231GapCarrier_card_le_four_scale4_gapMass",
        "cmp116Eq231SourcePIndex_mem_iff",
        "cmp116Eq231PIndex_eq_sourceFilteredBondSets_of_mem_iff",
        "CMP116Eq231PBondBoundary.of_balabanPFamilySourcePackage",
        "CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets",
        "CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_filteredBondSets",
    ]

    catalog = json.loads(
        (
            ROOT / "docs" / "source-db" / "catalogs" / "llm-operational-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    catalog_card = next(
        citation for citation in catalog["citations"] if citation["key"] == source_key
    )
    assert catalog_card["lean_targets"] == expected
    for target in stale:
        assert target not in catalog_card["lean_targets"]

    lean_crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    assert lean_crosswalk["counts"] == {
        "lean_targets": len(lean_crosswalk["targets"]),
        "links": sum(len(rows) for rows in lean_crosswalk["targets"].values()),
    }
    assert lean_crosswalk["counts"] == {"lean_targets": 83, "links": 131}

    lean_crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    assert "Unique Lean targets: **83**. Links: **131**." in lean_crosswalk_md

    for target in expected:
        assert any(
            item["citation_key"] == source_key
            for item in lean_crosswalk["targets"][target]
        )
        assert f"| `{target}` | `{source_key}` |" in lean_crosswalk_md
    for target in stale:
        assert all(
            item["citation_key"] != source_key
            for item in lean_crosswalk["targets"].get(target, [])
        )
        assert f"| `{target}` | `{source_key}` |" not in lean_crosswalk_md


def test_show_prints_eq237_local_routing_files(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.eq237.fixed-z0prime-source-estimate", path=output)
    captured = capsys.readouterr()
    assert "docs/source-db/indices/EQ237-POSTP-LIVE-FIELDS.md" in captured.out
    assert "docs/source-db/indices/EQ237-POSTP-PROOF-PROMPTS.md" in captured.out
    assert "docs/source-db/indices/EQ237-CITATION-EXTRACTION-REQUESTS.md" in captured.out
    assert "docs/source-db/indices/EQ237-DICTIONARY-COMMIT-QUEUE.md" in captured.out
    assert "consume the named fixed-Z0' display" in captured.out
    assert "Extract exact fixed-Z0' theorem shape" not in captured.out


def test_show_prints_eq229_local_routing_files(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.eq229.cammarota-dstage-summability", path=output)
    captured = capsys.readouterr()
    assert "docs/source-db/indices/EQ229-CAMMAROTA-LIVE-FIELDS.md" in captured.out
    assert "docs/source-db/indices/EQ229-CAMMAROTA-EXTRACTION-PROMPTS.md" in captured.out
    assert "docs/source-db/indices/EQ229-D-FAMILY-DICTIONARY-PLAN.md" in captured.out
    assert "docs/source-db/indices/CAMMAROTA-ACQUISITION-AND-CITATION-LEDGER.md" in captured.out


def test_show_prints_gaussian_root_local_routing_files(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.gaussian.root.localization-certificate", path=output)
    captured = capsys.readouterr()
    assert "docs/source-db/indices/GAUSSIAN-ROOT-HESSIAN-LIVE-FIELDS.md" in captured.out
    assert "docs/source-db/indices/GAUSSIAN-ROOT-HESSIAN-PROOF-PROMPTS.md" in captured.out
    assert "docs/source-db/indices/GAUSSIAN-ROOT-HESSIAN-COMMIT-QUEUE.md" in captured.out
    assert "docs/source-db/indices/RAW-SOURCE-M3-FIELD-ORDER.md" in captured.out


def test_show_prints_support_measurability_local_routing_files(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.activity.support-measurability.v2", path=output)
    captured = capsys.readouterr()
    assert "docs/source-db/indices/SUPPORT-MEASURABILITY-LIVE-FIELDS.md" in captured.out
    assert "docs/source-db/indices/SUPPORT-MEASURABILITY-PROOF-PROMPTS.md" in captured.out
    assert "docs/source-db/indices/GAUSSIAN-ROOT-HESSIAN-LIVE-FIELDS.md" in captured.out
    assert "docs/source-db/indices/RAW-SOURCE-M3-FIELD-ORDER.md" in captured.out


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


def test_show_surfaces_rawsource_m3_field_order_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.rawsource.m3.live-fields.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.rawsource.m3.live-fields.v2" in captured.out
    assert "status: lean_linked" in captured.out
    assert "covariance_root_certificate" in captured.out
    assert "gaussian_pushforward" in captured.out
    assert "raw_pointwise_decay" in captured.out
    assert "should not be discharged by one monolithic source citation" in captured.out
    assert "one source-looking package != proof of all raw_source fields" in captured.out
    assert "Exact source dictionary for physical fluctuation coordinates" in captured.out
    assert "Termwise norm estimate and raw_pointwise_decay" in captured.out
    assert "theorem_checked" not in captured.out


def test_rawsource_guard_live_fields_keep_qualified_lean_targets() -> None:
    expected_by_key = {
        "proof.rawsource.m3.live-fields.v2": [
            "YangMills.RG.BalabanCMP116SourceAssumptions",
            "YangMills.RG.CMP116RawSourceM3Frontier",
            "YangMills.RG.BalabanCMP116SourceTheorem",
            (
                "YangMills.RG."
                "PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses."
                "of_components"
            ),
        ],
        "proof.gaussian-root-hessian.commit-sequence.v2": [
            "YangMills.RG.BalabanCMP116SourceAssumptions",
            (
                "YangMills.RG."
                "PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses."
                "of_components"
            ),
            "YangMills.RG.CMP116RawSourceM3Frontier",
        ],
        "guard.no-final-bound-backfill.v2": [
            "YangMills.RG.BalabanCMP116SourceAssumptions",
            "YangMills.RG.CMP116RawSourceM3Frontier",
            "dimock-rg-i-iii-extracted",
        ],
    }
    stale_by_key = {
        "proof.rawsource.m3.live-fields.v2": [
            "BalabanCMP116SourceAssumptions",
            "CMP116RawSourceM3Frontier",
            "BalabanCMP116SourceTheorem",
            "PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_components",
        ],
        "proof.gaussian-root-hessian.commit-sequence.v2": [
            "BalabanCMP116SourceAssumptions",
            "PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_components",
            "CMP116RawSourceM3Frontier",
        ],
        "guard.no-final-bound-backfill.v2": [
            "BalabanCMP116SourceAssumptions",
            "CMP116RawSourceM3Frontier",
        ],
    }

    catalog = json.loads(
        (
            ROOT
            / "docs"
            / "source-db"
            / "catalogs"
            / "gaussian-root-hessian-live-fields.json"
        ).read_text(encoding="utf-8")
    )
    entries = {citation["key"]: citation for citation in catalog["citations"]}
    for source_key, expected in expected_by_key.items():
        assert entries[source_key]["lean_targets"] == expected
        for target in stale_by_key[source_key]:
            assert target not in entries[source_key]["lean_targets"]

    lean_crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    lean_crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    for source_key, expected in expected_by_key.items():
        for target in expected:
            if not target.startswith("YangMills."):
                continue
            assert target in lean_crosswalk["targets"]
            assert any(
                item["citation_key"] == source_key
                for item in lean_crosswalk["targets"][target]
            )
            assert f"| `{target}` | `{source_key}` |" in lean_crosswalk_md
        for target in stale_by_key[source_key]:
            assert all(
                item["citation_key"] != source_key
                for item in lean_crosswalk["targets"].get(target, [])
            )
            assert f"| `{target}` | `{source_key}` |" not in lean_crosswalk_md


def test_lean_lookup_finds_rawsource_m3_aggregate_targets(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("YangMills.RG.BalabanCMP116SourceTheorem", path=output)
    source_theorem = capsys.readouterr().out
    assert "proof.rawsource.m3.live-fields.v2 [lean_linked]" in source_theorem
    assert "Gaussian pushforward, covariance/root certificate" in source_theorem
    assert "Appendix-F/H# and flow remain ordered obligations" in source_theorem
    assert "no Lean target matches" not in source_theorem

    source_db.print_lean(
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses",
        path=output,
    )
    source_hypotheses = capsys.readouterr().out
    assert "crosswalk.final-frontier-pipeline [lean_linked]" in source_hypotheses
    assert "proof.rawsource.m3.live-fields.v2 [lean_linked]" in source_hypotheses
    assert "End-to-end operational dependency spine" in source_hypotheses
    assert "Batch 006 live-field map for the raw-source M3 frontier" in source_hypotheses
    assert "theorem_checked" not in source_hypotheses
    assert "no Lean target matches" not in source_hypotheses


def test_show_surfaces_source_status_promotion_gates(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.source-status-promotion.gates", path=output)
    captured = capsys.readouterr()
    assert "proof.source-status-promotion.gates" in captured.out
    assert "Current status: process_guardrail" in captured.out
    assert "source_extracted requires exact formula" in captured.out
    assert "assumptions, quantifiers, constants, dictionary" in captured.out
    assert "compiled Lean/oracle check for the named consumer" in captured.out
    for source_key in [
        "docs.SOURCE-CITATIONS",
        "docs.source-db.README",
    ]:
        assert source_key in captured.out
    for target in [
        "source_db.verify",
        "source_db.build",
        "oracle_check.lean",
    ]:
        assert target in captured.out
    for open_question in [
        "artifact hash",
        "visual page confirmation",
        "local_text/render locator",
        "Lean target link",
    ]:
        assert open_question in captured.out


def test_lean_lookup_finds_source_status_promotion_gate_targets(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("source_db.verify", path=output)
    verify = capsys.readouterr().out
    assert "proof.source-status-promotion.gates [lean_linked]" in verify
    assert "dictionary link: routes_to/operational" in verify
    assert "process_guardrail" in verify
    assert "no Lean target matches" not in verify

    source_db.print_lean("source_db.build", path=output)
    build = capsys.readouterr().out
    assert "proof.source-status-promotion.gates [lean_linked]" in build
    assert "dictionary link: also_routes_to/operational" in build
    assert "process_guardrail" in build
    assert "no Lean target matches" not in build

    source_db.print_lean("oracle_check.lean", path=output)
    oracle = capsys.readouterr().out
    assert "proof.source-status-promotion.gates [lean_linked]" in oracle
    assert "dictionary link: also_routes_to/operational" in oracle
    assert "process_guardrail" in oracle
    assert "Current status: process_guardrail" in oracle
    assert "no Lean target matches" not in oracle


def test_dependency_graph_keeps_raw_activity_source_blockers() -> None:
    graph = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "dependency-graph.json")
        .read_text(encoding="utf-8")
    )
    nodes = {node["id"]: node for node in graph["nodes"]}
    assert nodes["raw_activity"]["label"] == "RawYMActivityDecay / CMP116RawSourceM3Frontier"
    assert nodes["raw_activity"]["status"] == "Lean consumers saturated; source facts open"
    assert nodes["flow_ir"]["status"] == "source_pending"
    assert nodes["dimockF"]["status"] == "source_extracted"

    edges = {(edge["from"], edge["to"]): edge["label"] for edge in graph["edges"]}
    assert edges[("lemma3", "raw_activity")] == "activity decay package"
    assert edges[("dimockF", "raw_activity")] == "with-holes CE closure"
    assert edges[("cmp119_122", "raw_activity")] == "R/B/local remainder bounds"
    assert edges[("flow_ir", "raw_activity")] == "coupling and IR controls"
    assert edges[("raw_activity", "final")] == "feeds final frontier"

    graph_md = (
        ROOT / "docs" / "source-db" / "indices" / "DEPENDENCY-GRAPH.md"
    ).read_text(encoding="utf-8")
    assert "A node can be a navigation target without being theorem-feedable" in graph_md
    assert "Always inspect the node status and linked blocker entries" in graph_md
    assert "Lean consumers saturated; source facts open" in graph_md


def test_show_surfaces_final_frontier_pipeline_as_aggregate_only(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.final-frontier.pipeline", path=output)
    captured = capsys.readouterr()
    assert "proof.final-frontier.pipeline" in captured.out
    assert "status: lean_linked" in captured.out
    assert "Current status: aggregate_route" in captured.out
    assert "Use this only as a dashboard" in captured.out
    assert "implement the smallest upstream source theorem first" in captured.out
    assert "all higher-priority proof cards" in captured.out
    assert "source-fed Eq229 + Eq231 + Eq237" in captured.out
    assert "Gaussian/root/Hessian/H# + flow/IR" in captured.out
    assert "CMP116RawSourceM3Frontier" in captured.out
    assert "aggregate_route" in captured.out
    for source_key in [
        "crosswalk.final-frontier-pipeline",
        "cmp116.lemma3.final-2.38",
        "cmp116.effective-action.2.39-2.41",
    ]:
        assert source_key in captured.out
    for target in [
        "CMP116RawSourceM3Frontier",
        "BalabanCMP116SourceTheorem",
        "CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237",
    ]:
        assert target in captured.out
    assert "theorem_checked" not in captured.out


def test_final_frontier_crosswalk_keeps_qualified_lean_targets() -> None:
    source_key = "crosswalk.final-frontier-pipeline"
    expected = [
        "YangMills.RG.CMP116RawSourceM3Frontier",
        "YangMills.RG.BalabanCMP116SourceAssumptions",
        "YangMills.RG.RawYMActivityDecay",
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses",
    ]
    stale = [
        "CMP116RawSourceM3Frontier",
        "BalabanCMP116SourceAssumptions",
        "RawYMActivityDecay",
        "PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses",
    ]

    source_catalog = json.loads(
        (ROOT / "docs" / "source-db" / "catalogs" / "llm-operational-crosswalk.json")
        .read_text(encoding="utf-8")
    )
    source_entry = next(
        citation for citation in source_catalog["citations"] if citation["key"] == source_key
    )
    assert source_entry["lean_targets"] == expected
    for target in stale:
        assert target not in source_entry["lean_targets"]

    lean_crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    for target in expected:
        assert target in lean_crosswalk["targets"]
        assert any(
            item["citation_key"] == source_key
            for item in lean_crosswalk["targets"][target]
        )
    for target in stale:
        assert all(
            item["citation_key"] != source_key
            for item in lean_crosswalk["targets"].get(target, [])
        )

    lean_crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"| `{target}` | `{source_key}` |" in lean_crosswalk_md
    for target in stale:
        assert f"| `{target}` | `{source_key}` |" not in lean_crosswalk_md


def test_frontier_finds_cmp122_r_operation_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="cmp122", status="lean_linked", limit=30, path=output)
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "targets=8" in captured.out
    assert "questions=6" in captured.out
    assert "future_R_operation_bound" not in captured.out
    assert "CMP122-II Theorem 1 small-coupling hypotheses" in captured.out


def test_lean_lookup_finds_cmp122_source_dictionary_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("CMP119CMP122ERBSourceDecomposition", path=output)
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "CMP122-I/II and CMP119 localized R-operation bounds" in captured.out


def test_lean_lookup_finds_cmp122_component_estimates_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "CMP116Lemma3DeltaRlocComponentEstimates."
        "to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_weightTransport",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "visual_confirmed_but_dictionary_open" in captured.out


def test_lean_lookup_finds_cmp122_source_amplitude_activity_dictionary_route(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "CMP116Lemma3DeltaRlocSourceEstimates."
        "to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_"
        "weightTransport_amplitudeAndActivityDictionaries",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "source-certificate schema is split below without promoting any source fact" in captured.out
    assert "no Lean target matches" not in captured.out


def test_dimockiii_local_erb_targets_are_qualified_in_crosswalk() -> None:
    source_key = "dimockiii.theorem1.local-e-r-b-bounds.14-25"
    expected = [
        "YangMills.RG.RawYMActivityDecay",
        "YangMills.RG.PhysicalGaugeCMP116RawHsharpFrontier",
        "YangMills.RG.CMP116RawSourceM3Frontier",
    ]
    stale = [
        "RawYMActivityDecay",
        "PhysicalGaugeCMP116RawHsharpFrontier",
        "CMP116RawSourceM3Frontier",
    ]

    catalog = json.loads(
        (
            ROOT / "docs" / "source-db" / "catalogs" / "dimock-rg-i-iii-extracted.json"
        ).read_text(encoding="utf-8")
    )
    catalog_card = next(
        citation for citation in catalog["citations"] if citation["key"] == source_key
    )
    assert catalog_card["lean_targets"] == expected
    for target in stale:
        assert target not in catalog_card["lean_targets"]

    lean_crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    for target in expected:
        assert target in lean_crosswalk["targets"]
        assert any(
            item["citation_key"] == source_key
            for item in lean_crosswalk["targets"][target]
        )
    for target in stale:
        assert all(
            item["citation_key"] != source_key
            for item in lean_crosswalk["targets"].get(target, [])
        )

    lean_crosswalk_md = (
        ROOT / "docs" / "source-db" / "indices" / "LEAN-SOURCE-CROSSWALK.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"| `{target}` | `{source_key}` |" in lean_crosswalk_md
    for target in stale:
        assert f"| `{target}` | `{source_key}` |" not in lean_crosswalk_md


def test_lean_lookup_finds_qualified_cmp122_r_operation_routes(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("YangMills.RG.RawYMActivityDecay", path=output)
    captured = capsys.readouterr()
    assert "crosswalk.r-operation-polymer-local-route [lean_linked]" in captured.out
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "dimocki.small-field-cluster.235-237 [source_extracted]" in captured.out
    assert "dimockiii.theorem1.local-e-r-b-bounds.14-25 [source_extracted]" in captured.out
    assert "dictionary link: routes_to/operational" in captured.out
    assert "visual_confirmed_but_dictionary_open" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.RG.CMP116RawSourceM3Frontier", path=output)
    captured = capsys.readouterr()
    assert "crosswalk.r-operation-polymer-local-route [lean_linked]" in captured.out
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "dimockiii.theorem1.local-e-r-b-bounds.14-25 [source_extracted]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.RG.CMP119CMP122ERBSourceDecomposition", path=output)
    captured = capsys.readouterr()
    assert "cmp119.r-term-bound.2.31 [visual_confirmed]" in captured.out
    assert "cmp119.density-expansion-form.2.18 [visual_confirmed]" in captured.out
    assert (
        "cmp119.t-operation-action-factorization.2.19-2.23 [visual_confirmed]"
        in captured.out
    )
    assert "cmp119.e-term-local-regularity.2.24-2.29 [visual_confirmed]" in captured.out
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "visual_formula_field_extracted_dictionary_open" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.RG.CMP119BLocalSourceBound", path=output)
    captured = capsys.readouterr()
    assert "cmp119.b-term-local-regularity-bound.2.34-2.42 [visual_confirmed]" in captured.out
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3DeltaRlocSourceEstimates."
        "to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_"
        "cmp119BLocalSourceBound_weightTransport",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "CMP122-I/II and CMP119 localized R-operation bounds" in captured.out
    assert "located_not_fully_extracted" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3DeltaRlocSourceEstimates."
        "to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_sourceDictionaries",
        path=output,
    )
    captured = capsys.readouterr()
    assert (
        "YangMills.RG.CMP116Lemma3DeltaRlocSourceEstimates."
        "to_ERBComponentBoundary_of_cmp119CMP122SourceDecomposition_and_cmp119BLocalSourceBound_sourceDictionaries"
        in captured.out
    )
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "source-certificate schema is split below without promoting any source fact" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.lattice_mass_gap_of_per_scale_uv", path=output)
    captured = capsys.readouterr()
    assert "crosswalk.r-operation-polymer-local-route [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_cmp122_rloc_decay_source_anchor(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.rloc_decay",
        path=output,
    )
    captured = capsys.readouterr()
    assert "cmp122ii.eq1.98-1.100.r-operation-bound-source-target [visual_confirmed]" in captured.out
    assert "cmp122ii.rprime-bound.1.98-1.100 [visual_confirmed]" in captured.out
    assert "R/R-prime operation bounds feeding rloc_decay" in captured.out
    assert "dictionary identifying the R/R-prime operation bounds" in captured.out


def test_lean_lookup_finds_cmp122_post_r_decomposes_visual_anchor(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "YangMills.RG.PhysicalGaugeDimock318ERBComponentBoundary.decomposes",
        path=output,
    )
    captured = capsys.readouterr()
    assert "cmp122ii.eq1.101.post-r-erb-update-source-target [visual_confirmed]" in captured.out
    assert "cmp122ii.post-r-action-split.1.101 [visual_confirmed]" in captured.out
    assert "post-R action split with the Lean local-activity decomposition" in captured.out
    assert "dictionary identifying the post-R action split" in captured.out
    assert "no Lean target matches" not in captured.out


def test_search_finds_cmp122_post_r_action_dictionary(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("post-r action", path=output)
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "Source anchor for the post-R E/R/B update" in captured.out


def test_search_finds_cmp122_theorem1_small_coupling_handoff(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("coupling interval induction", path=output)
    captured = capsys.readouterr()
    assert "cmp122ii.theorem1.coupling-interval-induction [visual_confirmed]" in captured.out
    assert "effective coupling constants stay in a sufficiently small interval" in captured.out
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "source-certificate schema" in captured.out
    assert "RawYMActivityDecay proof" not in captured.out


def test_search_finds_cmp122_rprime_with_spaced_alias(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("cmp122 rprime", path=output)
    captured = capsys.readouterr()
    assert "cmp122ii.rprime-bound.1.98-1.100 [visual_confirmed]" in captured.out
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "located_not_fully_extracted" in captured.out


def test_frontier_surfaces_cmp122_visual_formula_lean_anchors(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="cmp122", status="visual_confirmed", limit=20, path=output)
    captured = capsys.readouterr()
    assert "cmp122ii.rprime-bound.1.98-1.100 [visual_confirmed] targets=1" in captured.out
    assert "cmp122ii.post-r-action-split.1.101 [visual_confirmed] targets=1" in captured.out
    assert "still needs the activity dictionary" in captured.out


def test_show_surfaces_cmp122_crosswalk_no_bare_scalar_guard(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("crosswalk.r-operation-polymer-local-route", path=output)
    captured = capsys.readouterr()
    assert "crosswalk.r-operation-polymer-local-route" in captured.out
    assert "status: lean_linked" in captured.out
    assert "avoiding a false bare scalar |R_k| <= M*r^k source claim" in captured.out
    assert "polymer-local exponential decay bounds" in captured.out
    assert "not a bare scalar geometric remainder" in captured.out
    assert "extra theorem/hypothesis" in captured.out
    assert "CMP119 Theorem 1" in captured.out
    assert "CMP122-II Theorem 1" in captured.out
    assert "RawYMActivityDecay" in captured.out
    assert "Source-to-Lean post-R action/local-activity dictionary" in captured.out
    assert "theorem_checked" not in captured.out


def test_show_surfaces_cmp122_source_certificate_schema_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.cmp122.r-operation-polymer-local-bound", path=output)
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound" in captured.out
    assert "source-certificate schema is split below without promoting any source fact" in captured.out
    assert "theorem1_hypotheses + rprime_bound + postR_split" in captured.out
    assert "source-to-Lean dictionary_open" in captured.out
    assert "source-to-Lean post-R action/local-activity dictionary" in captured.out
    assert "first group: X intersects Z_k^c union union_i Y_i" in captured.out
    assert "do not collapse them into RawYMActivityDecay or component decay" in captured.out
    assert "theorem_checked" not in captured.out


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


def test_lean_lookup_finds_eq237_global_z0prime_dictionary(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("cmp116Eq237SourceZ0PrimeIndex_eq_global_of_mem_iff", path=output)
    captured = capsys.readouterr()
    assert "proof.eq237.z0-z0prime-dictionary.v2 [lean_linked]" in captured.out
    assert "Dictionary target for D/P/Z0/Z0prime indices" in captured.out


def test_lean_lookup_finds_eq237_source_index_variants(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("YangMills.RG.cmp116Eq237Z0PrimeIndex", path=output)
    captured = capsys.readouterr()
    assert "cmp116.eq237.post-p-resummation [visual_confirmed]" in captured.out
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out
    assert "proof.eq237.z0-z0prime-dictionary.v2 [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.RG.cmp116Eq237Z0PrimeIndex_subset_global", path=output)
    captured = capsys.readouterr()
    assert "proof.eq237.z0-z0prime-dictionary.v2 [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237_sourceIndexMemIff",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.eq237.z0-z0prime-dictionary.v2 [lean_linked]" in captured.out
    assert "Dictionary target for D/P/Z0/Z0prime indices" in captured.out
    assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_eq237_lemma3_activity_endpoint(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-display.v2 [lean_linked]" in captured.out
    assert "proof.eq237.post-summation.final-z0prime.v2 [lean_linked]" in captured.out
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out


def test_lean_lookup_finds_qualified_eq237_fixed_z0prime_routes(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("YangMills.RG.cmp116Eq237Z0Fiber", path=output)
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out
    assert "CMP116 Eq. (2.37) fixed-Z0' source estimate" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.RG.cmp116PostPResidualSourceBound_of_eq237", path=output)
    captured = capsys.readouterr()
    assert "crosswalk.eq237.combined-postp-route [lean_linked]" in captured.out
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out
    assert "dictionary link: routes_to/operational" in captured.out
    assert "visual_confirmed_fixed_z0prime_display_dictionary_open" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions."
        "lemma3_activity_estimate_of_eq237",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_qualified_eq237_postp_live_fields(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("YangMills.RG.CMP116Eq237MajorizationBoundary", path=output)
    captured = capsys.readouterr()
    assert "crosswalk.eq237.combined-postp-route [lean_linked]" in captured.out
    assert "cmp116.eq237.post-p-resummation [visual_confirmed]" in captured.out
    assert "cmp116.eq232.z0-gap-distance-geometric [visual_confirmed]" in captured.out
    assert "cmp116.eq234.y0-subset-summation [visual_confirmed]" in captured.out
    assert "cmp116.eq236.scale-transfer-geometric [visual_confirmed]" in captured.out
    assert "cmp116.constants.c3-alpha5 [visual_confirmed]" in captured.out
    assert "proof.eq237.live-fields.v2 [lean_linked]" in captured.out
    assert "proof.eq237.fixed-z0prime-display.v2 [lean_linked]" in captured.out
    assert "proof.eq237.post-summation.final-z0prime.v2 [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3WeightedPostPSourceScaleBoundary.of_eq237",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.eq237.live-fields.v2 [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237",
        path=output,
    )
    captured = capsys.readouterr()
    assert "crosswalk.eq237.combined-postp-route [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions."
        "lemma3_activity_estimate_of_eq237",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out
    assert "proof.eq237.live-fields.v2 [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_eq237_subfield_blocker_routes(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    probes = [
        (
            "YangMills.RG.cmp116Eq237FixedZ0PrimeWeight",
            [
                "proof.eq237.component-product-to-family.v2 [lean_linked]",
                "proof.eq237.fixed-z0prime-display.v2 [lean_linked]",
                "dictionary link: also_routes_to/operational",
            ],
        ),
        (
            "YangMills.RG.cmp116Eq237Amplitude",
            [
                "proof.eq237.component-product-to-family.v2 [lean_linked]",
                "proof.eq237.constant-majorants.alpha5-c3.v2 [lean_linked]",
                "blocker: visual_confirmed_amplitude_majorization_open",
            ],
        ),
        (
            "YangMills.RG.cmp116Eq237_nested_sum_eq_fiber_sum",
            [
                "proof.eq237.z0-z0prime-dictionary.v2 [lean_linked]",
                "proof.eq237.fixed-z0prime-source-estimate [lean_linked]",
            ],
        ),
        (
            "YangMills.RG.cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237",
            [
                "proof.eq237.post-summation.final-z0prime.v2 [lean_linked]",
                "proof.eq237.residual-exponent-budget.v2 [lean_linked]",
            ],
        ),
        (
            "YangMills.RG.cmp116Eq237_residualExponent_absorbed",
            [
                "proof.eq237.post-summation.final-z0prime.v2 [lean_linked]",
                "proof.eq237.residual-exponent-budget.v2 [lean_linked]",
            ],
        ),
    ]

    for query, expected_snippets in probes:
        source_db.print_lean(query, path=output)
        captured = capsys.readouterr()
        for snippet in expected_snippets:
            assert snippet in captured.out
        assert "no Lean target matches" not in captured.out


def test_search_finds_eq237_combined_postp_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("cmp116PostPResidualSourceBound_of_eq237", path=output)
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out
    assert "CMP116 Eq. (2.37) fixed-Z0' source estimate" in captured.out


def test_search_finds_eq237_heq237_fixed_source_premise(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("heq237_fixed", path=output)
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-display.v2 [lean_linked]" in captured.out
    assert "fixed-Z0prime display" in captured.out


def test_search_finds_eq237_no_unsourced_splitting_guard(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("standalone normalized Z0", path=output)
    captured = capsys.readouterr()
    assert "guard.eq237.no-unsourced-splitting.v2 [lean_linked]" in captured.out
    assert "do not create standalone normalized Z0/Z0prime theorems" in captured.out
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out


def test_search_finds_eq237_clean_page_request(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("clean page19 20 excerpts", path=output)
    captured = capsys.readouterr()
    assert "request.eq237.clean-page19-20-excerpts.v2 [lean_linked]" in captured.out
    assert "Source-extraction request for CMP116 pages 19-20" in captured.out
    assert "post-(2.37) paragraph" in captured.out


def test_show_surfaces_eq237_fixed_z0prime_dictionary_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.eq237.fixed-z0prime-source-estimate", path=output)
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-source-estimate" in captured.out
    assert "status: lean_linked" in captured.out
    assert "source-display/dictionary blocker" in captured.out
    assert "fixed-Z0' Eq. (2.37) visual display" in captured.out
    assert "post-(2.37) final summation" in captured.out
    assert "Z0/Z0' source dictionary" in captured.out
    assert "visual_confirmed_fixed_z0prime_display_dictionary_open" in captured.out
    assert "visual_confirmed_constant_majorants_open" in captured.out
    assert "operational_crosswalk_dictionary_open" in captured.out
    assert "visual_confirmed_amplitude_majorization_open" in captured.out
    assert "D/P/Z0/Z0' dictionaries" in captured.out
    assert "component product over Zi'" in captured.out
    assert "post Eq. (2.37) half-exponent reserve" in captured.out
    assert "theorem_checked" not in captured.out


def test_show_surfaces_eq237_combined_postp_order_guard(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("crosswalk.eq237.combined-postp-route", path=output)
    captured = capsys.readouterr()
    assert "crosswalk.eq237.combined-postp-route" in captured.out
    assert "status: lean_linked" in captured.out
    assert (
        "Operational route for the combined post-P source bound after Eq. (2.37)."
        in captured.out
    )
    assert "combined, order-sensitive post-P boundary" in captured.out
    assert "rather than independent normalized Z0 and Z0' theorems" in captured.out
    assert "cmp116PostPResidualSourceBound_of_eq237" in captured.out
    assert "fixed-Z0' estimate plus final summation inputs" in captured.out
    assert (
        "fixed_Z0_prime_bound * final_Z0_prime_sum -> "
        "CMP116PostPResidualSourceBound"
    ) in captured.out
    assert "Exact fixed-Z0' source theorem" in captured.out
    assert "Exact final summation after Eq. (2.37)" in captured.out
    assert "theorem_checked" not in captured.out


def test_show_surfaces_eq237_residual_exponent_budget_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.eq237.residual-exponent-budget.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.eq237.residual-exponent-budget.v2" in captured.out
    assert "cmp116Eq237_residualExponent_absorbed" in captured.out
    assert "Do not reprove this as a new wrapper" in captured.out
    assert "seven_delta_decay + delta/2 residual_budget <= eight_delta_canonical_weight" in captured.out
    assert "Exact post-(2.37) final source summation and exponent-reserve step" in captured.out


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


def test_lean_lookup_finds_qualified_eq229_cammarota_routes(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("YangMills.RG.CammarotaCMP85FiniteDStageSource", path=output)
    captured = capsys.readouterr()
    assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in captured.out
    assert "CMP116 Eq. (2.29) D-stage product summability via Cammarota CMP85" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.RG.CMP116Lemma3Eq229ScaleBoundary", path=output)
    captured = capsys.readouterr()
    assert "crosswalk.eq229.cammarota-dstage-route [lean_linked]" in captured.out
    assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in captured.out
    assert "dictionary link: routes_to/operational" in captured.out
    assert "blocked_on_external_source" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "blocked_on_external_source" in captured.out
    assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_qualified_eq229_live_fields(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("YangMills.RG.CMP116Eq229Summability", path=output)
    summability = capsys.readouterr().out
    assert "crosswalk.eq229.cammarota-dstage-route [lean_linked]" in summability
    assert "proof.eq229.live-fields.v2 [lean_linked]" in summability
    assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in summability
    assert "cmp116.eq229.d-stage-summability [visual_confirmed]" in summability
    assert "cmp109.ref26.cammarota-infinite-range-cluster [visual_confirmed]" in summability
    assert "cammarota.cmp85.polymer-mayer-source-target [source_pending]" in summability
    assert "dictionary link: routes_to/operational" in summability
    assert "Primary-source theorem still must be extracted" in summability
    assert "no Lean target matches" not in summability

    source_db.print_lean("YangMills.RG.cmp116Eq229Product", path=output)
    product = capsys.readouterr().out
    assert "proof.eq229.live-fields.v2 [lean_linked]" in product
    assert "request.eq229.cmp116-local-excerpt-cleanup.v2 [lean_linked]" in product
    assert "no Lean target matches" not in product

    source_db.print_lean(
        "YangMills.RG.cmp116H_termWeightSum_le_of_eq229",
        path=output,
    )
    term_weight = capsys.readouterr().out
    assert "crosswalk.eq229.cammarota-dstage-route [lean_linked]" in term_weight
    assert "proof.eq229.live-fields.v2 [lean_linked]" in term_weight
    assert "proof.eq229.commit-sequence.v2 [lean_linked]" in term_weight
    assert "no Lean target matches" not in term_weight


def test_lean_lookup_finds_eq229_finite_discharge_live_fields(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    probes = [
        "YangMills.RG.cmp116Eq229Summability_of_product_majorant",
        "YangMills.RG.cmp116Eq229Summability_of_uniform_product_bound",
        "YangMills.RG.CammarotaCMP85Threshold.of_product_majorant",
        "YangMills.RG.CammarotaCMP85Threshold.of_uniform_product_bound",
        "YangMills.RG.CammarotaCMP85FiniteDStageSource",
        "YangMills.RG.CMP116Eq229Summability.of_cammarotaFiniteDStageSource",
        "YangMills.RG.CammarotaCMP85Threshold.of_finiteDStageSource",
    ]

    for query in probes:
        source_db.print_lean(query, path=output)
        captured = capsys.readouterr()
        assert "proof.eq229.live-fields.v2 [lean_linked]" in captured.out
        assert "Batch 005 live-field matrix for CMP116 Eq. (2.29)" in captured.out
        assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_eq229_proof_obligation_targets(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    probes = [
        "YangMills.RG.cmp116Eq229Weight",
        "YangMills.RG.CammarotaCMP85Threshold",
        "YangMills.RG.CMP116Eq229Summability.of_cammarotaThreshold",
        "YangMills.RG.cmp116Eq229Product_nonneg",
    ]

    for query in probes:
        source_db.print_lean(query, path=output)
        captured = capsys.readouterr()
        assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in captured.out
        assert (
            "Proof-obligation card: CMP116 Eq. (2.29) D-stage product "
            "summability via Cammarota CMP85."
        ) in captured.out
        assert "Current status: blocked_on_external_source" in captured.out
        assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_eq229_summability_guard(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("CMP116Eq229Summability", path=output)
    captured = capsys.readouterr()
    assert "guard.eq229.no-bibliographic-closure.v2 [lean_linked]" in captured.out
    assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in captured.out
    assert "Primary-source theorem still must be extracted" in captured.out


def test_search_finds_eq229_scale_boundary_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("CMP116Lemma3Eq229ScaleBoundary", path=output)
    captured = capsys.readouterr()
    assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in captured.out
    assert "CMP116 Eq. (2.29) D-stage product summability via Cammarota CMP85" in captured.out


def test_lean_lookup_finds_eq229_d_family_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("cmp116_DStage_sum_le_of_eq229", path=output)
    captured = capsys.readouterr()
    assert "proof.eq229.d-family.dictionary.v2 [lean_linked]" in captured.out
    assert "DIndex/DParts representation" in captured.out
    assert "argument/field surfaces in the Eq229 summability route" in captured.out
    assert "Exact source predicate for Balaban D-families" in captured.out


def test_show_surfaces_eq229_cammarota_external_source_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.eq229.cammarota-dstage-summability", path=output)
    captured = capsys.readouterr()
    assert "proof.eq229.cammarota-dstage-summability" in captured.out
    assert "status: lean_linked" in captured.out
    assert "Current status: blocked_on_external_source" in captured.out
    assert "CMP116Lemma3Eq229ScaleBoundary" in captured.out
    assert "CMP116Eq229Summability" in captured.out
    assert "DIndex/DParts dictionary" in captured.out
    assert "existing Eq. (1.4) premise field is not theorem evidence" in captured.out
    assert "Theorem 1 conclusion, hypotheses, constants" in captured.out
    assert "compatibility relation, uniformity" in captured.out
    assert "blocked_on_external_source" in captured.out
    assert "Cammarota theorem conclusion beyond the extracted Eq. (1.4) premise" in captured.out
    assert "Balaban D-family dictionary" in captured.out
    assert "metric d_k convention" in captured.out
    assert "theorem_checked" not in captured.out


def test_show_surfaces_eq229_cammarota_route_blockers(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("crosswalk.eq229.cammarota-dstage-route", path=output)
    captured = capsys.readouterr()
    assert "crosswalk.eq229.cammarota-dstage-route" in captured.out
    assert "status: lean_linked" in captured.out
    assert (
        "Operational route for theorem-feeding the CMP116 Eq. (2.29) "
        "D-stage summability through the Cammarota polymer/Mayer theorem."
    ) in captured.out
    assert "Cammarota's exact theorem, constants and polymer dictionary" in captured.out
    assert "still source_pending" in captured.out
    assert "sum_D prod_{Y in D} alpha6*exp(-delta*kappa*d_k(Y)) <= 1" in captured.out
    assert "YangMills.RG.CMP116Lemma3Eq229ScaleBoundary" in captured.out
    assert "YangMills.RG.CMP116Eq229Summability" in captured.out
    assert "YangMills.RG.cmp116H_termWeightSum_le_of_eq229" in captured.out
    assert "Balaban D-family -> DIndex/DParts [to_be_identified/pending]" in captured.out
    assert "Cammarota polymer dictionary and CMP116 D-family dictionary missing" in captured.out
    assert "Exact Cammarota theorem statement and uniform smallness threshold" in captured.out
    assert "Source-to-Lean dictionary from Cammarota polymers" in captured.out
    assert "theorem_checked" not in captured.out


def test_show_surfaces_eq229_threshold_dependency_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.eq229.thresholds.largeK-smallAlpha6.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.eq229.thresholds.largeK-smallAlpha6.v2" in captured.out
    assert "K sufficiently large and alpha6 sufficiently small" in captured.out
    assert "exists K0 alpha6Max" in captured.out
    assert "Primary-source theorem still must be extracted" in captured.out
    assert "Which parameters may K0 and alpha6Max depend on?" in captured.out
    assert "Uniformity over scale, volume and background field" in captured.out
    assert "theorem_checked" not in captured.out


def test_search_finds_eq229_cammarota_extraction_target(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("Mayer convergence theorem", path=output)
    captured = capsys.readouterr()
    assert "proof.eq229.cammarota.theorem1.extraction-target.v2 [lean_linked]" in captured.out
    assert "Cammarota CMP85 general polymer Mayer-series theorem" in captured.out
    assert "cammarota.cmp85.polymer-mayer-source-target [source_pending]" in captured.out
    assert "theorem_checked" not in captured.out


def test_search_finds_eq229_cammarota_half_rate_conclusion_caution(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("Cammarota Eq 1.11 half-rate conclusion", path=output)
    captured = capsys.readouterr()
    assert "proof.eq229.cammarota.theorem1.extraction-target.v2 [lean_linked]" in captured.out
    assert "Cammarota CMP85 general polymer Mayer-series theorem" in captured.out
    assert "theorem_checked" not in captured.out


def test_search_finds_eq229_cammarota_access_ledger(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("primary access ledger", path=output)
    captured = capsys.readouterr()
    assert "request.cammarota.primary-access.ledger.v2 [lean_linked]" in captured.out
    assert "non-duplication instructions" in captured.out
    assert "Cammarota CMP85 primary theorem text" in captured.out


def test_eq229_catalogs_do_not_reference_stale_symbols() -> None:
    stale_symbols = [
        "cmp116H_postD_sum_le_of_eq229",
        "CMP116WeightedPostPScaleSourceAssumptions",
    ]
    roots = [
        ROOT / "docs" / "source-db" / "catalogs",
        ROOT / "docs" / "source-db" / "indices",
        ROOT / "docs" / "source-citations",
    ]
    offenders = [
        f"{path.relative_to(ROOT).as_posix()}: {stale}"
        for root in roots
        for path in sorted(
            candidate
            for suffix in ("*.json", "*.md", "*.csv")
            for candidate in root.rglob(suffix)
        )
        for stale in stale_symbols
        if stale in path.read_text(encoding="utf-8")
    ]

    assert offenders == []


def test_frontier_finds_activity_termwise_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="activity", status="lean_linked", limit=30, path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "targets=12" in captured.out
    assert "questions=5" in captured.out
    assert "source-to-Lean index-stack identification for H(Z,Z0)/H(Z)" in captured.out


def test_lean_lookup_finds_activity_termwise_field(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "CMP116 H(Z) activity identification and termwise estimate" in captured.out
    assert "proof.raw-pointwise-decay.termwise.v2 [lean_linked]" in captured.out


def test_lean_lookup_finds_qualified_activity_termwise_routes(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "CMP116 H(Z) activity identification and termwise estimate" in captured.out
    assert "proof.activity.termwise.live-fields.v2 [lean_linked]" in captured.out
    assert "proof.raw-pointwise-decay.termwise.v2 [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary.activity_identification",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "proof.activity.termwise.live-fields.v2 [lean_linked]" in captured.out
    assert "proof.local-activity.construction.v2 [lean_linked]" in captured.out
    assert "dictionary link: routes_to/dictionary_open" in captured.out
    assert "source_to_lean_activity_identification_dictionary" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3PostPScaleSourceAssumptions.activityTermwiseBoundary",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "source_to_lean_activity_boundary_dictionary_open" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.RG.PhysicalGaugeLocalActivity.globalEval", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "proof.activity.termwise.live-fields.v2 [lean_linked]" in captured.out
    assert "proof.local-activity.construction.v2 [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "globalEval_activity_dictionary_open" in captured.out
    assert "cmp116.localized-activity.2.7-2.10 [visual_confirmed]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary",
        path=output,
    )
    captured = capsys.readouterr()
    assert "cmp116.localized-activity.2.7-2.10 [visual_confirmed]" in captured.out
    assert "cmp116.lemma3.window.2.14-2.38 [ocr_corrupted]" in captured.out
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_activity_termwise_downstream_source_fields(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.local_physical_activity_construction",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "proof.local-activity.construction.v2 [lean_linked]" in captured.out
    assert "dictionary link: routes_to/dictionary_open" in captured.out
    assert "source_to_lean_local_activity_construction_dictionary" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.RG.rawSource_of_lemma3ActivityEstimate", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "YangMills.RG.rawSource_of_lemma3ActivityEstimate_sourceRecords" in captured.out
    assert "proof.gaussian.pushforward.dictionary.v2 [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimateScaleFamily",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "CMP116 H(Z) activity identification and termwise estimate" in captured.out
    assert "theorem_checked" not in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_resummation",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "termwise_estimate_dictionary_open" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.CMP116Lemma3PostPScaleSourceAssumptions.lemma3_activity_estimate",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "source_to_lean_dictionary_blocker" in captured.out
    assert "theorem_checked" not in captured.out
    assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_activity_raw_source_record_fields(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.rawSource_of_lemma3ActivityEstimate_gaussianNormalization",
        path=output,
    )
    normalization = capsys.readouterr().out
    assert "proof.activity.termwise-identification [lean_linked]" in normalization
    assert (
        "Proof-obligation card: CMP116 H(Z) activity identification and "
        "termwise estimate."
    ) in normalization
    assert "Current status: source_to_lean_dictionary_blocker" in normalization
    assert "no Lean target matches" not in normalization

    source_db.print_lean(
        "YangMills.RG.rawSource_of_lemma3ActivityEstimate_sourceRecords",
        path=output,
    )
    records = capsys.readouterr().out
    assert "proof.activity.termwise-identification [lean_linked]" in records
    assert "proof.gaussian.pushforward.dictionary.v2 [lean_linked]" in records
    assert "Current status: source_to_lean_dictionary_blocker" in records
    assert "Gaussian pushforward equality after the covariance-root" in records
    assert "no Lean target matches" not in records


def test_search_finds_activity_termwise_boundary(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("CMP116Lemma3ActivityTermwiseScaleBoundary", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "CMP116 H(Z) activity identification and termwise estimate" in captured.out


def test_search_finds_activity_termwise_summand_identity(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("summand identity", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise.live-fields.v2 [lean_linked]" in captured.out
    assert "summand-identity" in captured.out


def test_show_surfaces_activity_field_uniformity_locator(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.activity.termwise.live-fields.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise.live-fields.v2" in captured.out
    assert "status: lean_linked" in captured.out
    assert "Dedicated live-field map for the CMP116 H(Z) activity-identification" in captured.out
    assert "H(Z,Z0), H(Z), and component-factorization displays" in captured.out
    assert "not a Lean activity dictionary" in captured.out
    assert "source-to-Lean summand dictionary" in captured.out
    assert "dictionary_open and does not discharge activity_identification" in captured.out
    assert "separate from the final Lemma 3 bound and from raw_pointwise_decay" in captured.out
    assert "U^c_{k+1}(X, alpha0, alpha1)" in captured.out
    assert "(2.20)/(2.22)" in captured.out
    assert "Eq. (2.29), Eq. (2.31), and Eq. (2.37)" in captured.out
    assert "PhysicalGaugeLocalActivity.globalEval" in captured.out
    assert "BalabanCMP116SourceAssumptions.raw_pointwise_decay" in captured.out
    assert "raw_pointwise_decay_requires_activity_and_eq229_eq231_eq237_dictionaries" in captured.out
    assert "dictionary_open" in captured.out
    assert "theorem_checked" not in captured.out


def test_show_surfaces_activity_termwise_dictionary_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.activity.termwise-identification", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification" in captured.out
    assert "source_to_lean_dictionary_blocker" in captured.out
    assert "render provenance only and not a source-to-Lean dictionary discharge" in captured.out
    assert "index-stack identification, summand identification, termWeight identification" in captured.out
    assert "component-factorization compatibility" in captured.out
    assert "U^c_{k+1}(X, alpha0, alpha1)" in captured.out
    assert "(2.20)/(2.22)" in captured.out
    assert "source_to_lean_activity_boundary_dictionary_open" in captured.out
    assert "theorem_checked" not in captured.out


def test_lean_lookup_finds_activity_termwise_boundary_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "CMP116Lemma3PostPScaleSourceAssumptions.activityTermwiseBoundary",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "source_to_lean_activity_boundary_dictionary_open" in captured.out


def test_lean_lookup_finds_activity_global_eval_dictionary_blocker(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("PhysicalGaugeLocalActivity.globalEval", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise-identification [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "globalEval_activity_dictionary_open" in captured.out


def test_lean_lookup_finds_activity_raw_decay_guard(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.raw_pointwise_decay",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.termwise.live-fields.v2 [lean_linked]" in captured.out
    assert "proof.raw-pointwise-decay.termwise.v2 [lean_linked]" in captured.out
    assert "dictionary link: guards/operational" in captured.out
    assert "raw_pointwise_decay_requires_activity_and_eq229_eq231_eq237_dictionaries" in captured.out
    assert "no Lean target matches" not in captured.out


def test_show_surfaces_raw_pointwise_termwise_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.raw-pointwise-decay.termwise.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.raw-pointwise-decay.termwise.v2" in captured.out
    assert "status: lean_linked" in captured.out
    assert "final raw_pointwise_decay field" in captured.out
    assert "does not prove the source termwise estimate" in captured.out
    assert "pointwise in t,k,X and physical fields" in captured.out
    assert "flattened D/P/Z0/Z0' summands" in captured.out
    assert "Eq. (2.29), Eq. (2.31), Eq. (2.37)" in captured.out
    assert "activity identification must be composed" in captured.out
    assert "BalabanCMP116SourceAssumptions.raw_pointwise_decay" in captured.out
    assert "Source termwise estimate for the actual CMP116 summand" in captured.out
    assert "Completion of Eq. (2.29), Eq. (2.31), Eq. (2.37) source dictionaries" in captured.out
    assert "theorem_checked" not in captured.out


def test_show_surfaces_no_final_bound_backfill_guard(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("guard.no-final-bound-backfill.v2", path=output)
    captured = capsys.readouterr()
    assert "guard.no-final-bound-backfill.v2" in captured.out
    assert "status: lean_linked" in captured.out
    assert "Final Lemma 3/H# estimates are downstream consumers" in captured.out
    assert "not proofs of Gaussian pushforward" in captured.out
    assert "covariance root, Hessian identity or physical activity construction" in captured.out
    assert "downstream estimate cannot prove upstream dictionary/root/Hessian fields" in captured.out
    assert "Dimock scalar RG architecture can guide theorem shape" in captured.out
    assert "not substitute YM source proof" in captured.out
    assert "BalabanCMP116SourceAssumptions" in captured.out
    assert "CMP116RawSourceM3Frontier" in captured.out
    assert "Exact source extraction for each upstream field" in captured.out
    assert "theorem_checked" not in captured.out


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


def test_lean_lookup_finds_gaussian_covariance_root_certificate(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("PhysicalLocalizedCovarianceRootCertificate", path=output)
    captured = capsys.readouterr()
    assert "proof.gaussian.covariance-root-certificate.v2 [lean_linked]" in captured.out
    assert "cmp95.covariance-green.bounds-source-target [visual_confirmed]" in captured.out
    assert "cmp96.one-step-covariance-law-source-target [located]" in captured.out
    assert "The Lean covariance-root dictionary remains open" in captured.out


def test_lean_lookup_finds_gaussian_covroot_source_assumption_consumer(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("BalabanCMP116SourceAssumptions.covariance_root_certificate", path=output)
    captured = capsys.readouterr()
    assert "proof.gaussian.covariance-root-certificate.v2 [lean_linked]" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "covariance_root_certificate_dictionary_open" in captured.out


def test_show_surfaces_gaussian_covariance_root_dictionary_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.gaussian.covariance-root-certificate.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.gaussian.covariance-root-certificate.v2" in captured.out
    assert "status: lean_linked" in captured.out
    assert "finite/physical covariance-root certificate" in captured.out
    assert (
        "CMP116 (2.5)-(2.6) is already the product-Gaussian pushforward anchor"
        in captured.out
    )
    assert "coordinate dictionary and determinant/Jacobian normalization open" in captured.out
    assert "guide for the certificate shape, not a Yang-Mills source proof" in captured.out
    assert "separates covariance/root certificate from gaussian_pushforward" in captured.out
    assert "and from root_localization" in captured.out
    assert "CMP96 one-step covariance law is located as metadata/label map only" in captured.out
    assert (
        "PhysicalLocalizedCovarianceRootCertificate precision covariance root "
        "covNormBound rootNormBound covWeight rootWeight"
    ) in captured.out
    assert (
        "Dimock II covariance-root resolvent != CMP116 Yang-Mills covariance-root proof"
        in captured.out
    )
    assert "covariance_root_certificate_dictionary_open" in captured.out
    assert "CMP95 G/G_k-to-repository covariance/root dictionary" in captured.out
    assert "CMP96 one-step covariance law" in captured.out
    assert "CMP99 background-field transport" in captured.out
    assert "PhysicalGaugeOneCochain coordinate dictionary" in captured.out
    assert "determinant/Jacobian boundary remain open" in captured.out
    assert "Exact operator equality/inequality fields" in captured.out
    assert "theorem_checked" not in captured.out


def test_show_surfaces_gaussian_pushforward_dictionary_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.gaussian.pushforward.dictionary.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.gaussian.pushforward.dictionary.v2" in captured.out
    assert "status: lean_linked" in captured.out
    assert "cmp116.gaussian-pushforward.2.5-2.6" in captured.out
    assert "source-to-Lean coordinate dictionary" in captured.out
    assert "determinant/Jacobian normalization" in captured.out
    assert "not the visual existence of the displayed pushforward step" in captured.out
    assert "gaussian_pushforward separately from root_localization" in captured.out
    assert "CMP116GaussianCoordinateMapSource" in captured.out
    assert "CMP116GaussianNormalizedPushforwardSource" in captured.out
    assert "theorem_checked" not in captured.out


def test_show_surfaces_root_localization_dictionary_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.root.localization.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.root.localization.v2" in captured.out
    assert "status: lean_linked" in captured.out
    assert "does not prove exact finite root-piece reconstruction" in captured.out
    assert "scalar analogy unless transported through the YM dictionary" in captured.out
    assert (
        "localized H(Z) display != exact finite root-piece reconstruction theorem"
        in captured.out
    )
    assert "root_localization_dictionary_open" in captured.out
    assert "physicalActiveSupport support/enlargement convention" in captured.out
    assert "uniform rootWeight/decay constants remain open" in captured.out
    assert "theorem_checked" not in captured.out


def test_lean_lookup_finds_qualified_gaussian_root_routes(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.PhysicalLocalizedCovarianceRootCertificate",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.gaussian.covariance-root-certificate.v2 [lean_linked]" in captured.out
    assert "proof.gaussian.root.localization-certificate [lean_linked]" in captured.out
    assert "dimocki.covariance-resolvent.334-335 [source_extracted]" in captured.out
    assert "dimockii.fluctuation-covariance.271-276 [source_extracted]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.covariance_root_certificate",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.gaussian.covariance-root-certificate.v2 [lean_linked]" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "covariance_root_certificate_dictionary_open" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.root_localization",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.gaussian.root.localization-certificate [lean_linked]" in captured.out
    assert "proof.root.localization.v2 [lean_linked]" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "root_localization_dictionary_open" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.root_localization",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.root.localization.v2 [lean_linked]" in captured.out
    assert "exact local root-piece reconstruction" in captured.out
    assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_gaussian_pushforward_dictionary_route(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.gaussian.pushforward.dictionary.v2 [lean_linked]" in captured.out
    assert "proof.gaussian.root.localization-certificate [lean_linked]" in captured.out
    assert "cmp98.eq14-15-source-target [located]" in captured.out


def test_lean_lookup_finds_qualified_gaussian_pushforward_dictionary(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.PhysicalGaugeCMP116Dictionary."
        "CMP116GaussianPushforwardNormalization.of_sourceRecords",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.gaussian.pushforward.dictionary.v2 [lean_linked]" in captured.out
    assert (
        "Gaussian pushforward equality after the covariance-root change of variables"
        in captured.out
    )
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses."
        "gaussian_pushforward",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.gaussian.pushforward.dictionary.v2 [lean_linked]" in captured.out
    assert "proof.gaussian.root.localization-certificate [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.gaussian_pushforward",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.gaussian.pushforward.dictionary.v2 [lean_linked]" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.RG.balabanCMP116Dmu0", path=output)
    captured = capsys.readouterr()
    assert "cmp116.gaussian-pushforward.2.5-2.6 [visual_confirmed]" in captured.out
    assert "proof.gaussian.pushforward.dictionary.v2 [lean_linked]" in captured.out
    assert "proof.gaussian.root.localization-certificate [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "source_to_lean_dictionary_blocker" in captured.out
    assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_gaussian_source_record_routes(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    probes = [
        "YangMills.RG.cmp116GaussianPushforwardNormalizationScaleFamily_of_sourceRecords",
        "YangMills.RG.rawSource_of_weightedPostPBoundaries_sourceRecords",
        "YangMills.RG.rawSource_of_eq231_weightedPostPBoundaries_sourceRecords",
        "YangMills.RG.rawSource_of_eq231_sourcePIndexMemIff_sourceRecords",
    ]

    for query in probes:
        source_db.print_lean(query, path=output)
        captured = capsys.readouterr()
        assert "proof.gaussian.pushforward.dictionary.v2 [lean_linked]" in captured.out
        assert (
            "Live-field card for the Gaussian pushforward equality after the "
            "covariance-root change of variables."
        ) in captured.out
        assert "theorem_checked" not in captured.out
        assert "no Lean target matches" not in captured.out


def test_search_finds_root_localization_field(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("root_localization", path=output)
    captured = capsys.readouterr()
    assert "proof.root.localization.v2 [lean_linked]" in captured.out
    assert "Live-field card for root localization" in captured.out


def test_lean_lookup_finds_gaussian_root_localization_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("BalabanCMP116SourceAssumptions.root_localization", path=output)
    captured = capsys.readouterr()
    assert "proof.gaussian.root.localization-certificate [lean_linked]" in captured.out
    assert "Gaussian pushforward and covariance-root localization certificate" in captured.out
    assert "proof.root.localization.v2 [lean_linked]" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "root_localization_dictionary_open" in captured.out


def test_lean_lookup_finds_raw_gaussian_root_localization_consumer(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.root_localization",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.root.localization.v2 [lean_linked]" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "exact local root-piece reconstruction" in captured.out


def test_search_finds_physical_precision_defect_hdefect_blocker(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("physicalPrecisionDefect hdefect", path=output)
    captured = capsys.readouterr()
    assert "proof.wilson.hessian.identification.v2 [lean_linked]" in captured.out
    assert "Wilson-Hessian interface" in captured.out
    assert "source-to-Lean coordinate, sign and normalization dictionary" in captured.out


def test_lean_lookup_finds_physical_precision_defect_hdefect_blocker(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "YangMills.RG.isCoerciveCLM_physicalPrecision_of_catalanMajorantPartial_defect",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.wilson.hessian.identification.v2 [lean_linked]" in captured.out
    assert "Wilson-Hessian interface" in captured.out
    assert "source-to-Lean coordinate, sign and normalization dictionary" in captured.out


def test_lean_lookup_finds_physical_precision_small_background_interface(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("YangMills.RG.SmallBackgroundPerturbation", path=output)
    captured = capsys.readouterr()
    assert "proof.wilson.hessian.identification.v2 [lean_linked]" in captured.out
    assert "operator-norm interface" in captured.out
    assert "Lean algebra bridge to the Catalan hdefect shape" in captured.out
    assert "do not by themselves prove the source small-background estimate" in captured.out


def test_lean_lookup_finds_physical_precision_small_background_hdefect_bridge(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "YangMills.RG.physicalPrecisionDefect_hdefect_of_smallBackgroundPerturbation",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.wilson.hessian.identification.v2 [lean_linked]" in captured.out
    assert "Lean algebra bridge to the Catalan hdefect shape" in captured.out
    assert "do not by themselves prove the source small-background estimate" in captured.out


def test_lean_lookup_finds_physical_precision_residual_budget_endpoints(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    targets = [
        "YangMills.RG.physicalPrecisionCatalanDefectCoercivityConstant_pos",
        "YangMills.RG.inner_physicalPrecision_pos_of_catalanMajorantPartial_defect",
        "YangMills.RG.covarianceOfPhysicalPrecisionCatalanDefect_comp_precision",
        "YangMills.RG.precision_comp_covarianceOfPhysicalPrecisionCatalanDefect",
        "YangMills.RG.norm_covarianceOfPhysicalPrecisionCatalanDefect_le",
        "YangMills.RG.covarianceOfPhysicalPrecisionCatalanDefect_psd",
    ]

    for target in targets:
        source_db.print_lean(target, path=output)
        captured = capsys.readouterr()
        assert "proof.wilson.hessian.identification.v2 [lean_linked]" in captured.out
        assert "positive residual-budget hypothesis hbudget is a separate blocker" in captured.out
        assert "no Lean target matches" not in captured.out


def test_lean_lookup_finds_wilson_hessian_source_anchor(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.wilson_hessian_identification",
        path=output,
    )
    captured = capsys.readouterr()
    assert "cmp102.variational-hessian-expansion-source-target [visual_confirmed]" in captured.out
    assert "proof.wilson.hessian.identification.v2 [lean_linked]" in captured.out
    assert "source-to-Lean coordinate, sign and normalization dictionary" in captured.out


def test_lean_lookup_finds_qualified_wilson_hessian_routes(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.wilson_hessian_identification",
        path=output,
    )
    balaban = capsys.readouterr().out
    assert "cmp102.variational-hessian-expansion-source-target [visual_confirmed]" in balaban
    assert "proof.wilson.hessian.identification.v2 [lean_linked]" in balaban
    assert "no Lean target matches" not in balaban

    source_db.print_lean(
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.wilson_hessian_identification",
        path=output,
    )
    raw = capsys.readouterr().out
    assert "cmp102.variational-hessian-expansion-source-target [visual_confirmed]" in raw
    assert "proof.wilson.hessian.identification.v2 [lean_linked]" in raw
    assert "no Lean target matches" not in raw

    source_db.print_lean("YangMills.RG.physicalGaugeWilsonHessianIdentification", path=output)
    alias = capsys.readouterr().out
    assert "cmp99.background-field-propagator-source-target [visual_confirmed]" in alias
    assert "cmp102.variational-hessian-expansion-source-target [visual_confirmed]" in alias
    assert "no Lean target matches" not in alias


def test_show_surfaces_wilson_hessian_physical_precision_blockers(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.wilson.hessian.identification.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.wilson.hessian.identification.v2" in captured.out
    assert "source-to-Lean coordinate, sign and normalization dictionary" in captured.out
    assert "SmallBackgroundPerturbation operator-norm interface" in captured.out
    assert "Lean algebra bridge to the Catalan hdefect shape" in captured.out
    assert "do not by themselves prove the source small-background estimate" in captured.out
    assert "does not prove the source-compatible operator-norm estimate" in captured.out
    assert "Catalan scalar comparison" in captured.out
    assert "positive residual-budget hypothesis hbudget is a separate blocker" in captured.out
    assert "schurCatalanBudget M epsilon < min 1 a / CP" in captured.out
    assert "CMP99 P1/P2/P3 precision cautions remain dictionary-facing only" in captured.out


def test_frontier_finds_activity_support_measurability_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="support", status="lean_linked", limit=30, path=output)
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "targets=7" in captured.out
    assert "questions=3" in captured.out
    assert "Exact enlargement convention" in captured.out


def test_search_finds_physical_active_support_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("physicalActiveSupport", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "Live-field card for support containment and measurability" in captured.out


def test_search_finds_support_measurable_summand_check(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("measurable summand", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "measurable-summand/finite-index" in captured.out


def test_show_surfaces_support_measurability_dictionary_blockers(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.activity.support-measurability.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2" in captured.out
    assert "status: lean_linked" in captured.out
    assert (
        "support containment and measurability of the physical local activity"
        in captured.out
    )
    assert "separates spectator_support_subset, fluctuation_support_subset" in captured.out
    assert (
        "activity_stronglyMeasurable from activity construction and raw decay"
        in captured.out
    )
    assert "physicalActiveSupport and PhysicalGaugeCMP116Dictionary" in captured.out
    assert (
        "source locality statements from being treated as measurability theorems"
        in captured.out
    )
    assert "does not follow from the finite-sum display alone" in captured.out
    assert (
        "(physicalActivity t k X).spectatorSupport subset physicalActiveSupport t k X"
        in captured.out
    )
    assert (
        "(physicalActivity t k X).fluctuationSupport subset physicalActiveSupport t k X"
        in captured.out
    )
    assert "StronglyMeasurable fun xi => adapted activity globalEval psi xi" in captured.out
    assert "support_measurability_support_dictionary_open" in captured.out
    assert "localized-domain to physicalActiveSupport enlargement" in captured.out
    assert "physicalBondsOfCells convention" in captured.out
    assert "skeleton HF X.val dictionary remain open" in captured.out
    assert "support_measurability_activity_measurability_dictionary_open" in captured.out
    assert "adapted activity measurability in CMP116FluctuationField" in captured.out
    assert "finite-index/measurable-summand data remain open" in captured.out
    assert "not a primary-source support theorem" in captured.out
    assert "Exact enlargement convention from source localized domains" in captured.out
    assert "Measurability proof for the adapted activity" in captured.out
    assert "Dictionary between source active sets and skeleton HF X.val" in captured.out
    assert "theorem_checked" not in captured.out


def test_support_measurability_catalog_keeps_live_field_gate() -> None:
    expected_lean_targets = [
        "YangMills.RG.BalabanCMP116SourceAssumptions.spectator_support_subset",
        "YangMills.RG.BalabanCMP116SourceAssumptions.fluctuation_support_subset",
        "YangMills.RG.BalabanCMP116SourceAssumptions.activity_stronglyMeasurable",
        "YangMills.RG.BalabanCMP116SourceAssumptions.active_support_subset_omega",
        "YangMills.RG.BalabanCMP116SourceAssumptions.active_support_subset_skeleton",
        "YangMills.RG.PhysicalGaugeCMP116Dictionary.physicalBondsOfCells",
        "YangMills.RG.PhysicalGaugeCMP116Dictionary.image_bondToCube_subset_iff_physicalBondsOfCells",
    ]
    stale_lean_targets = [
        "BalabanCMP116SourceAssumptions.spectator_support_subset",
        "BalabanCMP116SourceAssumptions.fluctuation_support_subset",
        "BalabanCMP116SourceAssumptions.activity_stronglyMeasurable",
        "BalabanCMP116SourceAssumptions.active_support_subset_omega",
        "BalabanCMP116SourceAssumptions.active_support_subset_skeleton",
    ]
    expected_formulas = [
        (
            "support.spectator.field",
            "(physicalActivity t k X).spectatorSupport subset physicalActiveSupport t k X",
            "Feeds spectator_support_subset.",
        ),
        (
            "support.fluctuation.field",
            "(physicalActivity t k X).fluctuationSupport subset physicalActiveSupport t k X",
            "Feeds fluctuation_support_subset.",
        ),
        (
            "support.measurable.field",
            "StronglyMeasurable fun xi => adapted activity globalEval psi xi",
            "Feeds activity_stronglyMeasurable.",
        ),
    ]
    expected_open_questions = [
        "Exact enlargement convention from source localized domains to physicalActiveSupport.",
        "Measurability proof for the adapted activity in CMP116FluctuationField.",
        "Dictionary between source active sets and skeleton HF X.val.",
    ]

    live_fields = json.loads(
        (
            ROOT
            / "docs"
            / "source-db"
            / "catalogs"
            / "gaussian-root-hessian-live-fields.json"
        ).read_text(encoding="utf-8")
    )
    support_card = next(
        card
        for card in live_fields["citations"]
        if card["key"] == "proof.activity.support-measurability.v2"
    )

    assert support_card["source_id"] == "repo_operational_crosswalk"
    assert support_card["status"] == "lean_linked"
    assert support_card["do_not_use_for"] == [
        "Do not infer support subset from decay alone."
    ]
    assert support_card["open_questions"] == expected_open_questions
    assert support_card["lean_targets"] == expected_lean_targets
    for target in stale_lean_targets:
        assert target not in support_card["lean_targets"]

    support_live_fields_md = (
        ROOT / "docs" / "source-db" / "indices" / "SUPPORT-MEASURABILITY-LIVE-FIELDS.md"
    ).read_text(encoding="utf-8")
    live_field_targets = [
        "`YangMills.RG.BalabanCMP116SourceAssumptions.spectator_support_subset`",
        "`YangMills.RG.BalabanCMP116SourceAssumptions.fluctuation_support_subset`",
        (
            "`YangMills.RG.BalabanCMP116SourceAssumptions.active_support_subset_omega`; "
            "`YangMills.RG.BalabanCMP116SourceAssumptions.active_support_subset_skeleton`"
        ),
        (
            "`YangMills.RG.PhysicalGaugeCMP116Dictionary.physicalBondsOfCells`; "
            "`YangMills.RG.PhysicalGaugeCMP116Dictionary."
            "image_bondToCube_subset_iff_physicalBondsOfCells`"
        ),
        "`YangMills.RG.BalabanCMP116SourceAssumptions.activity_stronglyMeasurable`",
    ]
    stale_live_field_rows = [
        (
            "| spectator support | source locality domain for spectator variables | "
            "`BalabanCMP116SourceAssumptions.spectator_support_subset` |"
        ),
        (
            "| fluctuation support | source locality domain for fluctuation variables | "
            "`BalabanCMP116SourceAssumptions.fluctuation_support_subset` |"
        ),
        (
            "| physical active support | source localized domains to repository "
            "`physicalActiveSupport` enlargement | `active_support_subset_omega`, "
            "`active_support_subset_skeleton` |"
        ),
        (
            "| skeleton convention | source active sets to "
            "`PhysicalGaugeCMP116Dictionary` physicalBondsOfCells / skeleton convention | "
            "`PhysicalGaugeCMP116Dictionary` support APIs |"
        ),
        (
            "| measurability | adapted physical local activity as a measurable function "
            "of fluctuation fields | "
            "`BalabanCMP116SourceAssumptions.activity_stronglyMeasurable` |"
        ),
    ]
    for target in live_field_targets:
        assert target in support_live_fields_md
    for row in stale_live_field_rows:
        assert row not in support_live_fields_md

    formulas = {formula["id"]: formula for formula in support_card["formulas"]}
    for formula_id, ascii_statement, conclusion in expected_formulas:
        formula = formulas[formula_id]
        assert formula["ascii"] == ascii_statement
        assert formula["conclusion"] == conclusion
        assert formula["exactness"] == "normalized_formula"
        assert formula["source_verified"] is False


def test_support_measurability_catalog_keeps_consumer_blockers() -> None:
    support_blocker = (
        "support_measurability_support_dictionary_open: localized-domain to "
        "physicalActiveSupport enlargement, physicalBondsOfCells convention, "
        "and skeleton HF X.val dictionary remain open."
    )
    measurability_blocker = (
        "support_measurability_activity_measurability_dictionary_open: adapted "
        "activity measurability in CMP116FluctuationField plus finite-index/"
        "measurable-summand data remain open."
    )

    live_fields = json.loads(
        (
            ROOT
            / "docs"
            / "source-db"
            / "catalogs"
            / "gaussian-root-hessian-live-fields.json"
        ).read_text(encoding="utf-8")
    )
    support_card = next(
        card
        for card in live_fields["citations"]
        if card["key"] == "proof.activity.support-measurability.v2"
    )
    links = {link["id"]: link for link in support_card["dictionary_links"]}

    expected = {
        "proof.activity.support-measurability.spectator-support-consumer": (
            "YangMills.RG.BalabanCMP116SourceAssumptions.spectator_support_subset",
            support_blocker,
        ),
        "proof.activity.support-measurability.fluctuation-support-consumer": (
            "YangMills.RG.BalabanCMP116SourceAssumptions.fluctuation_support_subset",
            support_blocker,
        ),
        "proof.activity.support-measurability.activity-measurable-consumer": (
            "YangMills.RG.BalabanCMP116SourceAssumptions.activity_stronglyMeasurable",
            measurability_blocker,
        ),
    }
    for link_id, (lean_symbol, blocker) in expected.items():
        link = links[link_id]
        assert link["source_symbol"] == "proof.activity.support-measurability.v2"
        assert link["lean_symbol"] == lean_symbol
        assert link["relation"] == "consumer_obligation"
        assert link["status"] == "lean_linked"
        assert link["blocker"] == blocker


def test_lean_lookup_finds_activity_measurability_field(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.activity_stronglyMeasurable",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "dictionary link: routes_to/dictionary_open" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "source_to_lean_measurability_dictionary" in captured.out
    assert "support_measurability_activity_measurability_dictionary_open" in captured.out


def test_lean_lookup_finds_activity_support_field_blockers(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.spectator_support_subset",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "support_measurability_support_dictionary_open" in captured.out


def test_lean_lookup_finds_fluctuation_support_field_blockers(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.fluctuation_support_subset",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "dictionary link: routes_to/dictionary_open" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "source_to_lean_support_dictionary" in captured.out
    assert "support_measurability_support_dictionary_open" in captured.out


def test_lean_lookup_finds_active_support_dictionary_routes(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.active_support_subset_omega",
        path=output,
    )
    omega = capsys.readouterr().out
    assert "proof.activity.support-measurability.v2 [lean_linked]" in omega
    assert "dictionary link: also_routes_to/operational" in omega
    assert "source_to_lean_support_dictionary" in omega
    assert "no Lean target matches" not in omega

    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.active_support_subset_skeleton",
        path=output,
    )
    skeleton = capsys.readouterr().out
    assert "proof.activity.support-measurability.v2 [lean_linked]" in skeleton
    assert "dictionary link: also_routes_to/operational" in skeleton
    assert "source_to_lean_support_dictionary" in skeleton
    assert "no Lean target matches" not in skeleton


def test_lean_lookup_finds_support_physical_bonds_repository_api(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.PhysicalGaugeCMP116Dictionary.physicalBondsOfCells",
        path=output,
    )
    physical_bonds = capsys.readouterr().out
    assert "proof.activity.support-measurability.v2 [lean_linked]" in physical_bonds
    assert "dictionary link: repository_api/operational" in physical_bonds
    assert "source_to_lean_support_dictionary" in physical_bonds
    assert "no Lean target matches" not in physical_bonds

    source_db.print_lean(
        "YangMills.RG.PhysicalGaugeCMP116Dictionary."
        "image_bondToCube_subset_iff_physicalBondsOfCells",
        path=output,
    )
    subset_bridge = capsys.readouterr().out
    assert "proof.activity.support-measurability.v2 [lean_linked]" in subset_bridge
    assert "dictionary link: repository_api/operational" in subset_bridge
    assert "source_to_lean_support_dictionary" in subset_bridge
    assert "no Lean target matches" not in subset_bridge


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
    assert "Dimock Appendix F H# feed/route into hole-cluster machinery" in captured.out


def test_search_finds_appendixf_hsharp_feed_alias(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("H# feed", path=output)
    captured = capsys.readouterr()
    assert "proof.dimock.appendixf.hsharp-feed [lean_linked]" in captured.out
    assert "H# feed/route" in captured.out


def test_show_surfaces_appendixf_hsharp_feed_dictionary_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.dimock.appendixf.hsharp-feed", path=output)
    captured = capsys.readouterr()
    assert "proof.dimock.appendixf.hsharp-feed" in captured.out
    assert "Current status: partially_source_extracted" in captured.out
    assert "H# feed" in captured.out
    assert "does not prove the Appendix-F consumer" in captured.out
    assert "hsharp_feed_dictionary_open" in captured.out
    assert "activity bound |H(X)| <= H0 exp(-kappa d_M)" in captured.out
    assert "H0 <= c0" in captured.out
    assert "kappa >= 3*kappa0+3" in captured.out
    assert "Omega-connectivity" in captured.out
    assert "skeleton metric dictionary remain open" in captured.out
    for source_key in [
        "crosswalk.dimock.appendixf-hole-cluster-route",
        "dimockii.appendix-f.cluster-with-holes",
        "dimockii.appendix-f.second-ursell.645-646",
    ]:
        assert source_key in captured.out
    for target in [
        "YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound",
        "YangMills.RG.balabanCMP116AppendixFHsharpOfIntegratedKsharp",
        "YangMills.RG.appendixFHoleExpWeight",
    ]:
        assert target in captured.out
    for open_question in [
        "activity/locality estimate",
        "Omega-connectivity relation",
        "skeleton metric dictionary",
    ]:
        assert open_question in captured.out
    assert "without promoting upstream raw-source fields" in captured.out
    assert "theorem_checked" not in captured.out


def test_show_surfaces_rooted_hsharp_remainder_dictionary_blocker(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.rooted-hsharp-remainder.identity.v2", path=output)
    captured = capsys.readouterr()
    assert "proof.rooted-hsharp-remainder.identity.v2" in captured.out
    assert "status: lean_linked" in captured.out
    assert "rooted_hsharp_remainder_identity" in captured.out
    assert "physical Yang-Mills raw source scale family" in captured.out
    assert "should not be used to backfill Gaussian pushforward" in captured.out
    assert "rawSource components before rooted H# remainder identity" in captured.out
    assert (
        "    - YangMills.RG.BalabanCMP116SourceAssumptions."
        "rooted_hsharp_remainder_identity"
    ) in captured.out
    assert "    - YangMills.RG.balabanCMP116AppendixFHsharpOfIntegratedKsharp" in captured.out
    assert "    - YangMills.RG.physicalGaugeCMP116RawSourceScaleFamily" in captured.out
    assert (
        "    - BalabanCMP116SourceAssumptions.rooted_hsharp_remainder_identity"
    ) not in captured.out.splitlines()
    assert "    - balabanCMP116AppendixFHsharpOfIntegratedKsharp" not in captured.out.splitlines()
    assert "    - physicalGaugeCMP116RawSourceScaleFamily" not in captured.out.splitlines()
    assert "Exact source theorem for the rooted H# representation" in captured.out
    assert "skeleton/Omega connectivity" in captured.out
    assert "Summability and real-part normalization" in captured.out
    assert "theorem_checked" not in captured.out


def test_rooted_hsharp_remainder_routes_second_ursell_outside_lean_targets() -> None:
    catalog = json.loads(
        (
            ROOT
            / "docs"
            / "source-db"
            / "catalogs"
            / "gaussian-root-hessian-live-fields.json"
        ).read_text(encoding="utf-8")
    )
    card = next(
        entry
        for entry in catalog["citations"]
        if entry["key"] == "proof.rooted-hsharp-remainder.identity.v2"
    )
    source_key = "dimockii.appendix-f.second-ursell.645-646"

    assert source_key not in card["lean_targets"]
    assert {
        (link["source_symbol"], link["lean_symbol"], link["status"], link["blocker"])
        for link in card["dictionary_links"]
        if link["id"] == "rooted-hsharp.second-ursell-anchor"
    } == {
        (
            source_key,
            "YangMills.RG.BalabanCMP116SourceAssumptions.rooted_hsharp_remainder_identity",
            "dictionary_open",
            "rooted_hsharp_remainder_dictionary_open",
        )
    }


def test_lean_lookup_finds_qualified_rooted_hsharp_remainder_targets(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions."
        "rooted_hsharp_remainder_identity",
        path=output,
    )
    rooted = capsys.readouterr().out
    assert "proof.rooted-hsharp-remainder.identity.v2 [lean_linked]" in rooted
    assert "Live-field card for the rooted H# identity" in rooted
    assert "no Lean target matches" not in rooted

    source_db.print_lean("YangMills.RG.physicalGaugeCMP116RawSourceScaleFamily", path=output)
    scale_family = capsys.readouterr().out
    assert "proof.rooted-hsharp-remainder.identity.v2 [lean_linked]" in scale_family
    assert "raw-source scale family" in scale_family
    assert "no Lean target matches" not in scale_family

    source_db.print_lean("YangMills.RG.balabanCMP116AppendixFHsharpOfIntegratedKsharp", path=output)
    hsharp_adapter = capsys.readouterr().out
    assert "proof.rooted-hsharp-remainder.identity.v2 [lean_linked]" in hsharp_adapter
    assert "proof.dimock.appendixf.hsharp-feed [lean_linked]" in hsharp_adapter
    assert "no Lean target matches" not in hsharp_adapter


def test_lean_lookup_finds_appendixf_hsharp_feed_link(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("balabanCMP116AppendixFHsharpOfIntegratedKsharp", path=output)
    captured = capsys.readouterr()
    assert "proof.dimock.appendixf.hsharp-feed [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "partially_source_extracted" in captured.out
    assert "hsharp_feed_dictionary_open" in captured.out


def test_lean_lookup_finds_appendixf_hsharp_kp_blocker(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound", path=output)
    captured = capsys.readouterr()
    assert "proof.dimock.appendixf.hsharp-feed [lean_linked]" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "hsharp_feed_dictionary_open" in captured.out


def test_lean_lookup_finds_qualified_appendixf_crosswalk_routes(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    summary = "Dimock II Appendix F through the repository's omega-hole polymer KP layer"

    source_db.print_lean(
        "YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp",
        path=output,
    )
    skeleton_exp = capsys.readouterr().out
    assert "crosswalk.dimock.appendixf-hole-cluster-route [lean_linked]" in skeleton_exp
    assert (
        "YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp"
        in skeleton_exp
    )
    assert summary in skeleton_exp
    assert "no Lean target matches" not in skeleton_exp

    source_db.print_lean("YangMills.RG.AppendixFHsharpLeafSource", path=output)
    leaf_source = capsys.readouterr().out
    assert "crosswalk.dimock.appendixf-hole-cluster-route [lean_linked]" in leaf_source
    assert "YangMills.RG.AppendixFHsharpLeafSource" in leaf_source
    assert summary in leaf_source
    assert "no Lean target matches" not in leaf_source


def test_lean_lookup_finds_qualified_appendixf_hsharp_routes(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound",
        path=output,
    )
    kp = capsys.readouterr().out
    assert "proof.dimock.appendixf.hsharp-feed [lean_linked]" in kp
    assert "dictionary link: routes_to/operational" in kp
    assert "dictionary link: consumer_obligation/lean_linked" in kp
    assert "hsharp_feed_dictionary_open" in kp
    assert "no Lean target matches" not in kp

    source_db.print_lean("YangMills.RG.balabanCMP116AppendixFHsharpOfIntegratedKsharp", path=output)
    integrated = capsys.readouterr().out
    assert "proof.dimock.appendixf.hsharp-feed [lean_linked]" in integrated
    assert "dictionary link: also_routes_to/operational" in integrated
    assert "dictionary link: consumer_obligation/lean_linked" in integrated
    assert "hsharp_feed_dictionary_open" in integrated
    assert "no Lean target matches" not in integrated

    source_db.print_lean("YangMills.RG.appendixFHoleExpWeight", path=output)
    exp_weight = capsys.readouterr().out
    assert "proof.dimock.appendixf.hsharp-feed [lean_linked]" in exp_weight
    assert "dictionary link: also_routes_to/operational" in exp_weight
    assert "dictionary link: consumer_obligation/lean_linked" in exp_weight
    assert "hsharp_feed_dictionary_open" in exp_weight
    assert "no Lean target matches" not in exp_weight


def test_lean_lookup_finds_qualified_dimock_metric_cover_route(
    tmp_path: Path, capsys
) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean(
        "YangMills.RG.norm_appendixFConnectedActivity_le_metricCoverSum",
        path=output,
    )
    captured = capsys.readouterr()
    assert "dimocki.cluster-expansion.theorem27.296-299 [source_extracted]" in captured.out
    assert "dimockii.appendix-f.metric-first-activity.637-644 [source_extracted]" in captured.out
    assert "Standard ultralocal cluster-expansion theorem" in captured.out
    assert "no Lean target matches" not in captured.out


def test_frontier_finds_flow_ir_bridge_card(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_frontier(term="flow", status="lean_linked", limit=30, path=output)
    captured = capsys.readouterr()
    assert "proof.flow.ir.bridge [lean_linked] targets=6" in captured.out
    assert "questions=3" in captured.out
    assert "CMP109/CMP119 beta-function source" in captured.out


def test_search_finds_flow_ir_bridge_route(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("ir bridge", path=output)
    captured = capsys.readouterr()
    assert "proof.flow.ir.bridge [lean_linked]" in captured.out
    assert "Flow and IR bridge separating marginal logarithmic flow" in captured.out


def test_show_surfaces_flow_ir_dictionary_blocker(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_show("proof.flow.ir.bridge", path=output)
    captured = capsys.readouterr()
    assert "proof.flow.ir.bridge" in captured.out
    assert "Current status: conceptual_bridge_blocker" in captured.out
    assert "marginal g_k decays logarithmically" in captured.out
    assert "geometric r^k belongs to irrelevant remainders/operators" in captured.out
    assert "not the gauge coupling itself" in captured.out
    assert "flow_ir_dictionary_open" in captured.out
    assert "CMP109/CMP119 beta-function source extraction" in captured.out
    assert "source-to-Lean coupling recursion dictionary" in captured.out
    assert "irrelevant operator scaling theorem" in captured.out
    assert "IR covariance decay remain open" in captured.out
    assert "covIR, hIRbound, and the coupling recursion explicit" in captured.out
    assert "rather than g_k <= C*r^k" in captured.out
    assert "crosswalk.flow-ir-asymptotic-freedom-route" in captured.out
    for target in [
        "YangMills.RG.logistic_geometric_decay",
        "YangMills.RG.remainder_geometric_of_logistic",
        "YangMills.RG.BalabanCMP116SourceAssumptions.coupling_recursion",
        "YangMills.RG.BalabanCMP116SourceAssumptions.ir_bound",
        "YangMills.RG.lattice_mass_gap_of_singleScaleUVDecay_marginal",
        "YangMills.RG.marginal_coupling_remainder_tsum_le_of_recursion",
    ]:
        assert target in captured.out
    for open_question in [
        "CMP109/CMP119 beta-function source",
        "irrelevant operator scaling theorem",
        "IR covariance decay",
    ]:
        assert open_question in captured.out
    assert "without promoting the logistic/geometric surrogate" in captured.out
    assert "they do not discharge the missing CMP109/CMP119 Flow/IR dictionary" in captured.out
    assert "theorem_checked" not in captured.out


def test_lean_lookup_finds_flow_ir_bridge_blocker(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("BalabanCMP116SourceAssumptions.coupling_recursion", path=output)
    captured = capsys.readouterr()
    assert "proof.flow.ir.bridge [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "conceptual_bridge_blocker" in captured.out
    assert "flow_ir_dictionary_open" in captured.out


def test_lean_lookup_finds_qualified_flow_ir_routes(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("YangMills.RG.logistic_geometric_decay", path=output)
    logistic = capsys.readouterr().out
    assert "crosswalk.flow-ir-asymptotic-freedom-route [lean_linked]" in logistic
    assert "proof.flow.ir.bridge [lean_linked]" in logistic
    assert "no Lean target matches" not in logistic

    source_db.print_lean("YangMills.RG.remainder_geometric_of_logistic", path=output)
    irrelevant_remainder = capsys.readouterr().out
    assert (
        "crosswalk.flow-ir-asymptotic-freedom-route [lean_linked]"
        in irrelevant_remainder
    )
    assert "proof.flow.ir.bridge [lean_linked]" in irrelevant_remainder
    assert "no Lean target matches" not in irrelevant_remainder

    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.ir_bound",
        path=output,
    )
    ir_bound = capsys.readouterr().out
    assert "crosswalk.flow-ir-asymptotic-freedom-route [lean_linked]" in ir_bound
    assert "proof.flow.ir.bridge [lean_linked]" in ir_bound
    assert "flow_ir_dictionary_open" in ir_bound
    assert "no Lean target matches" not in ir_bound

    source_db.print_lean(
        "YangMills.RG.BalabanCMP116SourceAssumptions.coupling_recursion",
        path=output,
    )
    recursion = capsys.readouterr().out
    assert "proof.flow.ir.bridge [lean_linked]" in recursion
    assert "dictionary link: also_routes_to/operational" in recursion
    assert "dictionary link: consumer_obligation/lean_linked" in recursion
    assert "conceptual_bridge_blocker" in recursion
    assert "flow_ir_dictionary_open" in recursion
    assert "no Lean target matches" not in recursion

    source_db.print_lean(
        "YangMills.RG.lattice_mass_gap_of_singleScaleUVDecay_marginal",
        path=output,
    )
    marginal = capsys.readouterr().out
    assert "proof.flow.ir.bridge [lean_linked]" in marginal
    assert "dictionary link: also_routes_to/operational" in marginal
    assert "dictionary link: consumer_obligation/lean_linked" in marginal
    assert "conceptual_bridge_blocker" in marginal
    assert "flow_ir_dictionary_open" in marginal
    assert "no Lean target matches" not in marginal

    source_db.print_lean(
        "YangMills.RG.marginal_coupling_remainder_tsum_le_of_recursion",
        path=output,
    )
    remainder = capsys.readouterr().out
    assert "proof.flow.ir.bridge [lean_linked]" in remainder
    assert "dictionary link: also_routes_to/operational" in remainder
    assert "dictionary link: consumer_obligation/lean_linked" in remainder
    assert "conceptual_bridge_blocker" in remainder
    assert "flow_ir_dictionary_open" in remainder
    assert "no Lean target matches" not in remainder


def test_search_finds_flow_ir_single_scale_marginal_consumer(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_search("SingleScaleUVDecay marginal covIR", path=output)
    captured = capsys.readouterr()
    assert "proof.flow.ir.bridge [lean_linked]" in captured.out
    assert "Flow and IR bridge separating marginal logarithmic flow" in captured.out


def test_lean_lookup_finds_flow_ir_marginal_consumer_context(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("marginal_coupling_remainder_tsum_le_of_recursion", path=output)
    captured = capsys.readouterr()
    assert "proof.flow.ir.bridge [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "conceptual_bridge_blocker" in captured.out
    assert "flow_ir_dictionary_open" in captured.out


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


def test_auxiliary_matrices_track_cmp96_located_label_map() -> None:
    blocker = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "blocker-matrix.json").read_text(
            encoding="utf-8"
        )
    )
    cmp96_blocker = next(
        item
        for item in blocker["blockers"]
        if item["citation_key"] == "cmp96.one-step-covariance-law-source-target"
    )
    assert cmp96_blocker["status"] == "located"
    assert "key labels 230" in cmp96_blocker["printed_pages"]
    assert "formula bodies remain visual-only" in cmp96_blocker["summary"]

    coverage = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "paper-coverage-matrix.json").read_text(
            encoding="utf-8"
        )
    )
    cmp96_coverage = next(
        item for item in coverage["coverage"] if item["source_id"] == "cmp96"
    )
    assert cmp96_coverage["catalog_status"] == "located-label-map"
    assert "formula bodies not extracted" in cmp96_coverage["formula_status"]

    blocker_md = (
        ROOT / "docs" / "source-db" / "indices" / "BLOCKER-MATRIX.md"
    ).read_text(encoding="utf-8")
    assert (
        "| 6 | `cmp96.one-step-covariance-law-source-target` | `located` |"
        in blocker_md
    )

    coverage_md = (
        ROOT / "docs" / "source-db" / "indices" / "PAPER-COVERAGE-MATRIX.md"
    ).read_text(encoding="utf-8")
    assert "`cmp96` — Balaban CMP96 | located-label-map |" in coverage_md


def test_blocker_matrix_keeps_core_source_pending_gates() -> None:
    blocker = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "blocker-matrix.json").read_text(
            encoding="utf-8"
        )
    )
    by_key = {item["citation_key"]: item for item in blocker["blockers"]}
    expected_pending = {
        "cammarota.cmp85.polymer-mayer-source-target": (
            "Cammarota CMP85",
            "Theorem statement, smallness, constants, metric and uniformity.",
        ),
        "cmp109.bond-convention.positive-oriented": (
            "Balaban CMP109",
            "Bridge from the general convention",
        ),
        "cmp116.eq231.p-family-carrier-source-target": (
            "Balaban CMP116",
            "Membership iff.",
        ),
        "cmp98.eq14-15-source-target": (
            "Balaban CMP98",
            "Exact formula transcription and surrounding definitions.",
        ),
    }

    for citation_key, (short, first_question) in expected_pending.items():
        item = by_key[citation_key]
        assert item["status"] == "source_pending"
        assert item["short"] == short
        assert item["questions"][0].startswith(first_question)

    blocker_md = (
        ROOT / "docs" / "source-db" / "indices" / "BLOCKER-MATRIX.md"
    ).read_text(encoding="utf-8")
    assert "Non-theorem-feedable entries and first actions." in blocker_md
    for citation_key, (short, _) in expected_pending.items():
        assert f"| `{citation_key}` | `source_pending` | {short} |" in blocker_md

    crosswalk = json.loads(
        (
            ROOT / "docs" / "source-db" / "indices" / "lean-source-crosswalk.json"
        ).read_text(encoding="utf-8")
    )
    cmp98_pushforward = next(
        item
        for item in crosswalk["targets"]["gaussian_pushforward"]
        if item["citation_key"] == "cmp98.eq14-15-source-target"
    )
    assert cmp98_pushforward["status"] == "located"
    assert "formula bodies and dictionary remain open" in cmp98_pushforward["summary"]


def test_paper_coverage_matrix_keeps_cmp122_pipeline_gates() -> None:
    coverage = json.loads(
        (ROOT / "docs" / "source-db" / "indices" / "paper-coverage-matrix.json")
        .read_text(encoding="utf-8")
    )
    by_source = {item["source_id"]: item for item in coverage["coverage"]}

    cmp122_ii = by_source["cmp122_ii"]
    assert cmp122_ii["catalog_status"] == "seeded"
    assert "Theorem 1 and Eqs. (1.98)-(1.101) visually confirmed" in cmp122_ii[
        "formula_status"
    ]
    assert "dictionary still open" in cmp122_ii["formula_status"]
    assert "Extract exact Theorem 1 small-coupling constants" in cmp122_ii[
        "next_action"
    ]
    assert "CMP119 Sect. 2 condition dictionary" in cmp122_ii["next_action"]

    cmp122_i = by_source["cmp122_i"]
    assert cmp122_i["catalog_status"] == "seeded"
    assert "Eq. (1.70) large-field C_k bound visually confirmed" in cmp122_i[
        "formula_status"
    ]
    assert "exact hypotheses and post-R dictionary still open" in cmp122_i[
        "formula_status"
    ]
    assert "without promoting it to RawYMActivityDecay" in cmp122_i["next_action"]

    cmp119 = by_source["cmp119"]
    assert cmp119["catalog_status"] == "structured-minimal"
    assert cmp119["formula_status"] == "minimal"
    assert "E/R/B decomposition and Eq. (2.42)" in cmp119["next_action"]

    coverage_md = (
        ROOT / "docs" / "source-db" / "indices" / "PAPER-COVERAGE-MATRIX.md"
    ).read_text(encoding="utf-8")
    assert "`cmp122_ii` — Balaban CMP122-II | seeded |" in coverage_md
    assert "dictionary still open | local-pdf-text-renders-present" in coverage_md
    assert "without promoting it to RawYMActivityDecay" in coverage_md
