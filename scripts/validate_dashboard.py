#!/usr/bin/env python3
"""Validate docs/dashboard/data.json against the repository tree.

The dashboard is public-facing, but its data is curated by humans.  This script
checks the mechanical invariants: schema, path existence, acyclicity, milestone
consistency, and the single live-frontier marker.

Run from the repo root:

    python scripts/validate_dashboard.py
"""

from __future__ import annotations

import datetime as _dt
import json
import pathlib
import sys
from collections import Counter, deque
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parent.parent
DATA = ROOT / "docs" / "dashboard" / "data.json"

STATUSES = {"proved", "partial", "open"}
CLASSES = {"A", "B", "C", "D"}
REQUIRED_META = {
    "title",
    "subtitle",
    "updated",
    "checkpoint",
    "axioms",
    "clay_distance",
    "m3_estimate",
    "frontier",
    "repo",
    "blob",
    "ledger",
    "horizon",
    "knowledge_tree",
    "dashboard_url",
}
REQUIRED_NODE = {"id", "label", "status", "cls", "group", "col", "row", "note"}
REQUIRED_MILESTONES = {"M0", "M1", "M2", "M3", "M4", "M5"}


errors: list[str] = []


def err(message: str) -> None:
    errors.append(message)


def repo_path_exists(rel: str) -> bool:
    rel_path = pathlib.PurePosixPath(rel)
    if rel_path.is_absolute() or ".." in rel_path.parts:
        return False
    return (ROOT / pathlib.Path(*rel_path.parts)).exists()


def require_dict(value: Any, name: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        err(f"{name} must be an object")
        return {}
    return value


def require_list(value: Any, name: str) -> list[Any]:
    if not isinstance(value, list):
        err(f"{name} must be an array")
        return []
    return value


def validate_meta(data: dict[str, Any]) -> dict[str, Any]:
    meta = require_dict(data.get("meta"), "meta")
    for key in sorted(REQUIRED_META):
        if key not in meta:
            err(f"meta.{key} missing")
    try:
        _dt.date.fromisoformat(str(meta.get("updated", "")))
    except ValueError:
        err(f"meta.updated is not an ISO date: {meta.get('updated')!r}")
    if not isinstance(meta.get("m3_estimate"), int):
        err("meta.m3_estimate must be an integer")
    return meta


def validate_groups(data: dict[str, Any]) -> set[str]:
    groups = require_list(data.get("groups"), "groups")
    ids: list[str] = []
    for i, group in enumerate(groups):
        group_obj = require_dict(group, f"groups[{i}]")
        gid = group_obj.get("id")
        if not isinstance(gid, str) or not gid:
            err(f"groups[{i}].id must be a nonempty string")
        else:
            ids.append(gid)
        if not isinstance(group_obj.get("label"), str) or not group_obj.get("label"):
            err(f"groups[{i}].label must be a nonempty string")
    counts = Counter(ids)
    for gid, count in counts.items():
        if count > 1:
            err(f"duplicate group id: {gid}")
    return set(ids)


def validate_nodes(data: dict[str, Any], group_ids: set[str]) -> list[dict[str, Any]]:
    nodes_raw = require_list(data.get("nodes"), "nodes")
    nodes: list[dict[str, Any]] = []
    ids: list[str] = []
    slots: dict[tuple[int, int], str] = {}

    for i, node in enumerate(nodes_raw):
        n = require_dict(node, f"nodes[{i}]")
        nodes.append(n)
        nid = n.get("id", f"<node {i}>")
        if not isinstance(nid, str) or not nid:
            err(f"nodes[{i}].id must be a nonempty string")
            continue
        ids.append(nid)
        missing = REQUIRED_NODE - n.keys()
        for field in sorted(missing):
            err(f"node {nid}: missing field {field!r}")
        if n.get("status") not in STATUSES:
            err(f"node {nid}: invalid status {n.get('status')!r}")
        if n.get("cls") not in CLASSES:
            err(f"node {nid}: invalid class {n.get('cls')!r}")
        if n.get("group") not in group_ids:
            err(f"node {nid}: unknown group {n.get('group')!r}")
        col, row = n.get("col"), n.get("row")
        if not isinstance(col, int) or not isinstance(row, int) or col < 0 or row < 0:
            err(f"node {nid}: col and row must be nonnegative integers")
        else:
            slot = (col, row)
            if slot in slots:
                err(f"node {nid}: slot {slot} collides with node {slots[slot]}")
            slots[slot] = nid
        links = require_list(n.get("links", []), f"node {nid}.links")
        for j, link in enumerate(links):
            link_obj = require_dict(link, f"node {nid}.links[{j}]")
            if not isinstance(link_obj.get("label"), str) or not link_obj.get("label"):
                err(f"node {nid}: link {j} is missing a label")
            is_ledger = bool(link_obj.get("ledger"))
            rel = link_obj.get("path") or link_obj.get("tree")
            if is_ledger:
                continue
            if not isinstance(rel, str) or not rel:
                err(f"node {nid}: link {link_obj.get('label')!r} has no path/tree/ledger")
                continue
            if not repo_path_exists(rel):
                err(f"node {nid}: linked path does not exist in repo: {rel}")

    counts = Counter(ids)
    for nid, count in counts.items():
        if count > 1:
            err(f"duplicate node id: {nid}")
    frontier_nodes = [n.get("id") for n in nodes if n.get("frontier") is True]
    if len(frontier_nodes) != 1:
        err(f"expected exactly one frontier node, found {frontier_nodes}")
    return nodes


def validate_edges(data: dict[str, Any], nodes: list[dict[str, Any]]) -> None:
    node_ids = {n.get("id") for n in nodes if isinstance(n.get("id"), str)}
    adj: dict[str, list[str]] = {node_id: [] for node_id in node_ids}
    indeg: dict[str, int] = {node_id: 0 for node_id in node_ids}

    edges = require_list(data.get("edges"), "edges")
    for i, edge in enumerate(edges):
        e = require_dict(edge, f"edges[{i}]")
        source, target = e.get("from"), e.get("to")
        if source not in node_ids:
            err(f"edge {source}->{target}: unknown source node")
            continue
        if target not in node_ids:
            err(f"edge {source}->{target}: unknown target node")
            continue
        adj[source].append(target)
        indeg[target] += 1

    queue = deque(sorted(node_id for node_id, degree in indeg.items() if degree == 0))
    seen = 0
    while queue:
        current = queue.popleft()
        seen += 1
        for nxt in adj[current]:
            indeg[nxt] -= 1
            if indeg[nxt] == 0:
                queue.append(nxt)
    if seen != len(node_ids):
        err("dependency graph contains a cycle")


def validate_milestones(data: dict[str, Any], meta: dict[str, Any]) -> None:
    milestones_raw = require_list(data.get("milestones"), "milestones")
    milestones: dict[str, dict[str, Any]] = {}
    for i, milestone in enumerate(milestones_raw):
        m = require_dict(milestone, f"milestones[{i}]")
        mid = m.get("id")
        if not isinstance(mid, str) or not mid:
            err(f"milestones[{i}].id must be a nonempty string")
            continue
        milestones[mid] = m
        pct = m.get("pct")
        if not isinstance(pct, int) or not 0 <= pct <= 100:
            err(f"milestone {mid}: pct out of range: {pct!r}")
        if m.get("status") not in STATUSES:
            err(f"milestone {mid}: invalid status {m.get('status')!r}")
    missing = REQUIRED_MILESTONES - milestones.keys()
    extra = milestones.keys() - REQUIRED_MILESTONES
    for mid in sorted(missing):
        err(f"milestone {mid} missing")
    for mid in sorted(extra):
        err(f"unexpected milestone {mid}")
    m3 = milestones.get("M3", {})
    if m3.get("pct") != meta.get("m3_estimate"):
        err("meta.m3_estimate disagrees with milestone M3 pct")


def main() -> int:
    try:
        data = json.loads(DATA.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001
        print(f"FATAL: cannot parse {DATA}: {exc}", file=sys.stderr)
        return 1

    data_obj = require_dict(data, "dashboard data")
    meta = validate_meta(data_obj)
    group_ids = validate_groups(data_obj)
    nodes = validate_nodes(data_obj, group_ids)
    validate_edges(data_obj, nodes)
    validate_milestones(data_obj, meta)

    if errors:
        print(f"validate_dashboard: {len(errors)} problem(s)")
        for message in errors:
            print(f"  - {message}")
        return 1

    status_counts = Counter(n["status"] for n in nodes)
    edge_count = len(data_obj.get("edges", []))
    print(
        "validate_dashboard: OK - "
        f"{len(nodes)} nodes "
        f"({status_counts.get('proved', 0)} proved / "
        f"{status_counts.get('partial', 0)} partial / "
        f"{status_counts.get('open', 0)} open), "
        f"{edge_count} edges, DAG acyclic, all linked paths exist."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
