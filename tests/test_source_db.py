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
    source_keys = [
        "cmp119.r-term-bound.2.31",
        "cmp122i.large-field-c-bound.1.70",
        "cmp122ii.rprime-bound.1.98-1.100",
        "crosswalk.r-operation-polymer-local-route",
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

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md


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


def test_eq237_indices_keep_qualified_lean_targets() -> None:
    expected = [
        "YangMills.RG.cmp116PostPResidualSourceBound_of_eq237",
        "YangMills.RG.CMP116Eq237MajorizationBoundary",
        "YangMills.RG.cmp116Eq237FixedZ0PrimeWeight",
        "YangMills.RG.cmp116Eq237Amplitude",
    ]
    proof_key = "proof.eq237.fixed-z0prime-source-estimate"
    source_keys = [
        "cmp116.eq237.post-p-resummation",
        "cmp116.constants.c3-alpha5",
        "crosswalk.eq237.combined-postp-route",
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

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md


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
    source_keys = [
        "cmp116.eq229.d-stage-summability",
        "cmp109.ref26.cammarota-infinite-range-cluster",
        "cammarota.cmp85.polymer-mayer-source-target",
        "crosswalk.eq229.cammarota-dstage-route",
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

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md


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

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md


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

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    assert "`YangMills.RG.logistic_geometric_decay`" in hypothesis_queue_md
    assert (
        "`YangMills.RG.BalabanCMP116SourceAssumptions.coupling_recursion`"
        in hypothesis_queue_md
    )


def test_gaussian_root_indices_keep_qualified_lean_targets() -> None:
    expected = [
        "YangMills.RG.PhysicalLocalizedCovarianceRootCertificate",
        "YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward",
        "YangMills.RG.balabanCMP116Dmu0",
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

    hypothesis_queue_md = (
        ROOT / "docs" / "source-db" / "indices" / "HYPOTHESIS-REMOVAL-QUEUE.md"
    ).read_text(encoding="utf-8")
    for source_key in source_keys:
        assert f"`{source_key}`" in hypothesis_queue_md
    for target in expected:
        assert f"`{target}`" in hypothesis_queue_md


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


def test_lean_lookup_finds_qualified_cmp122_r_operation_routes(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("YangMills.RG.RawYMActivityDecay", path=output)
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "dimocki.small-field-cluster.235-237 [source_extracted]" in captured.out
    assert "dimockiii.theorem1.local-e-r-b-bounds.14-25 [source_extracted]" in captured.out
    assert "dictionary link: routes_to/operational" in captured.out
    assert "visual_confirmed_but_dictionary_open" in captured.out
    assert "no Lean target matches" not in captured.out

    source_db.print_lean("YangMills.RG.CMP119CMP122ERBSourceDecomposition", path=output)
    captured = capsys.readouterr()
    assert "proof.cmp122.r-operation-polymer-local-bound [lean_linked]" in captured.out
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "visual_formula_field_extracted_dictionary_open" in captured.out
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


def test_lean_lookup_finds_cmp122_rloc_decay_source_anchor(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("PhysicalGaugeDimock318ERBComponentBoundary.rloc_decay", path=output)
    captured = capsys.readouterr()
    assert "cmp122ii.eq1.98-1.100.r-operation-bound-source-target [visual_confirmed]" in captured.out
    assert "R/R-prime operation bounds feeding rloc_decay" in captured.out
    assert "dictionary identifying the R/R-prime operation bounds" in captured.out


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
        "YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions."
        "lemma3_activity_estimate_of_eq237",
        path=output,
    )
    captured = capsys.readouterr()
    assert "proof.eq237.fixed-z0prime-source-estimate [lean_linked]" in captured.out
    assert "proof.eq237.live-fields.v2 [lean_linked]" in captured.out
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
    assert "proof.eq229.live-fields.v2 [lean_linked]" in summability
    assert "proof.eq229.cammarota-dstage-summability [lean_linked]" in summability
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
    assert "proof.eq229.live-fields.v2 [lean_linked]" in term_weight
    assert "proof.eq229.commit-sequence.v2 [lean_linked]" in term_weight
    assert "no Lean target matches" not in term_weight


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
    assert "Exact source predicate for Balaban D-families" in captured.out


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
        ROOT / "docs" / "source-citations",
    ]
    offenders = [
        f"{path.relative_to(ROOT).as_posix()}: {stale}"
        for root in roots
        for path in sorted(root.rglob("*.json"))
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
    source_db.print_lean("CMP116Lemma3ActivityTermwiseScaleBoundary.termwise_estimate", path=output)
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
    assert "dictionary link: also_routes_to/operational" in captured.out
    assert "globalEval_activity_dictionary_open" in captured.out
    assert "no Lean target matches" not in captured.out


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
    assert "U^c_{k+1}(X, alpha0, alpha1)" in captured.out
    assert "(2.20)/(2.22)" in captured.out
    assert "dictionary_open" in captured.out


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
    source_db.print_lean("BalabanCMP116SourceAssumptions.raw_pointwise_decay", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.termwise.live-fields.v2 [lean_linked]" in captured.out
    assert "dictionary link: guards/operational" in captured.out
    assert "raw_pointwise_decay_requires_activity_and_eq229_eq231_eq237_dictionaries" in captured.out


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


def test_lean_lookup_finds_activity_measurability_field(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("BalabanCMP116SourceAssumptions.activity_stronglyMeasurable", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "dictionary link: routes_to/dictionary_open" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "source_to_lean_measurability_dictionary" in captured.out
    assert "support_measurability_activity_measurability_dictionary_open" in captured.out


def test_lean_lookup_finds_activity_support_field_blockers(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("BalabanCMP116SourceAssumptions.spectator_support_subset", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "support_measurability_support_dictionary_open" in captured.out


def test_lean_lookup_finds_fluctuation_support_field_blockers(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)
    source_db.print_lean("BalabanCMP116SourceAssumptions.fluctuation_support_subset", path=output)
    captured = capsys.readouterr()
    assert "proof.activity.support-measurability.v2 [lean_linked]" in captured.out
    assert "dictionary link: routes_to/dictionary_open" in captured.out
    assert "dictionary link: consumer_obligation/lean_linked" in captured.out
    assert "source_to_lean_support_dictionary" in captured.out
    assert "support_measurability_support_dictionary_open" in captured.out


def test_lean_lookup_finds_active_support_dictionary_routes(tmp_path: Path, capsys) -> None:
    output = tmp_path / "index.sqlite"
    source_db.build_database(output=output, root=ROOT)

    source_db.print_lean("BalabanCMP116SourceAssumptions.active_support_subset_omega", path=output)
    omega = capsys.readouterr().out
    assert "proof.activity.support-measurability.v2 [lean_linked]" in omega
    assert "dictionary link: also_routes_to/operational" in omega
    assert "source_to_lean_support_dictionary" in omega
    assert "no Lean target matches" not in omega

    source_db.print_lean("BalabanCMP116SourceAssumptions.active_support_subset_skeleton", path=output)
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
