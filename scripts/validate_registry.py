#!/usr/bin/env python3
"""
validate_registry.py — Registry consistency checker for THE ERIKSSON PROGRAMME.

Checks:
  1. All node statuses are listed in registry/labels.yaml::status_labels
  2. All dependency from/to references resolve to known node IDs
  3. Critical-path BLACKBOX nodes have a bottlenecks.yaml entry
  4. Nodes with axiom evidence flag mathlib_gap or clay_gap

Structural note (2026-03-29): nodes.yaml uses a dict-keyed mapping
  nodes:
    L0.1:
      status: FORMALIZED_KERNEL
      ...
yaml.safe_load returns {"nodes": {"L0.1": {...}, "L0.2": {...}, ...}}.
Iterating a dict gives string keys, not node dicts — hence the original
AttributeError crash. normalise_nodes() converts to a list transparently.
"""
import os
import sys
import yaml
from pathlib import Path
from itertools import chain


def _repo_root() -> Path:
    """
    Locate the repository root.  Tries in order:

    1. __file__  — when running as `python scripts/validate_registry.py`
    2. ERIKSSON_REPO_ROOT env var  — explicit override
    3. Walk upward from cwd looking for lakefile.lean  — catches `%cd repo_root`
    4. Check cwd / 'THE-ERIKSSON-PROGRAMME'  — Colab default clone location
    5. Walk upward from cwd looking for registry/nodes.yaml  — last resort
    6. cwd  — fallback (will show a clear error if still wrong)
    """
    # 1. Script mode (__file__ is defined)
    try:
        candidate = Path(__file__).resolve().parent.parent
        if (candidate / "lakefile.lean").exists():
            return candidate
    except NameError:
        pass

    # 2. Explicit env var
    env = os.environ.get("ERIKSSON_REPO_ROOT")
    if env:
        return Path(env).resolve()

    # 3. Walk up from cwd looking for lakefile.lean
    cwd = Path.cwd().resolve()
    for ancestor in [cwd, *cwd.parents]:
        if (ancestor / "lakefile.lean").exists():
            return ancestor

    # 4. Sibling: cwd / 'THE-ERIKSSON-PROGRAMME'  (Colab: clone into /content/...)
    sibling = cwd / "THE-ERIKSSON-PROGRAMME"
    if (sibling / "lakefile.lean").exists():
        return sibling

    # 5. Walk up looking for registry/nodes.yaml
    for ancestor in [cwd, *cwd.parents]:
        if (ancestor / "registry" / "nodes.yaml").exists():
            return ancestor

    # 6. Give up — return cwd and let load_yaml emit the clear error message
    return cwd


def load_yaml(path_str: str, required: bool = True) -> dict:
    p = Path(path_str)
    if not p.exists():
        if required:
            print(f"❌ Required file not found: {path_str}")
            sys.exit(1)
        return {}
    data = yaml.safe_load(p.read_text(encoding="utf-8"))
    return data or {}


def normalise_nodes(raw) -> list:
    """
    Accept both:
      - dict format: {id: {status: ..., ...}, ...}   (current nodes.yaml)
      - list format: [{id: ..., status: ..., ...}, ...]  (future-compatible)
    Always returns a list of dicts each containing an 'id' key.
    """
    if isinstance(raw, dict):
        return [{"id": k, **v} for k, v in raw.items()]
    if isinstance(raw, list):
        return list(raw)
    return []


def main() -> None:
    REPO_ROOT = _repo_root()

    def R(rel: str) -> str:
        return str(REPO_ROOT / rel)

    nodes_raw      = load_yaml(R("registry/nodes.yaml"),          required=True)
    deps_raw       = load_yaml(R("registry/dependencies.yaml"),   required=True)
    critical_raw   = load_yaml(R("registry/critical_paths.yaml"), required=False)
    labels         = load_yaml(R("registry/labels.yaml"),         required=True)
    bottlenecks_r  = load_yaml(R("registry/bottlenecks.yaml"),    required=False)

    nodes        = normalise_nodes(nodes_raw.get("nodes", {}))
    deps         = deps_raw.get("dependencies", [])
    critical     = (critical_raw or {}).get("critical_paths", [])
    valid_status = set(labels.get("status_labels", []))
    bottlenecks  = (bottlenecks_r or {}).get("bottlenecks", [])

    node_ids = {n["id"] for n in nodes}
    cp_nodes = set(chain.from_iterable(p.get("nodes", []) for p in critical))

    errors: list = []

    # ── 1. Valid statuses ────────────────────────────────────────────────────
    if valid_status:
        for n in nodes:
            s = n.get("status")
            if s not in valid_status:
                errors.append(
                    f"[STATUS] Node {n['id']}: status {s!r} not in "
                    f"labels.yaml::status_labels {sorted(valid_status)}"
                )
    else:
        print("⚠️  labels.yaml has no status_labels — skipping status check")

    # ── 2. Dependency from/to references exist in nodes.yaml ─────────────────
    for dep in deps:
        for field in ("from", "to"):
            ref = dep.get(field)
            if ref and ref not in node_ids:
                errors.append(
                    f"[DEP]    {dep.get('from')} → {dep.get('to')}: "
                    f"node {ref!r} missing from nodes.yaml"
                )

    # ── 3. Critical-path BLACKBOX nodes need a bottlenecks.yaml entry ─────────
    for n in nodes:
        if n["id"] in cp_nodes and n.get("status") == "BLACKBOX":
            registered = any(
                n["id"] in (b.get("related_nodes") or [])
                for b in bottlenecks
            )
            if not registered:
                errors.append(
                    f"[CRIT]   Node {n['id']} is BLACKBOX on critical path "
                    f"but has no bottlenecks.yaml entry"
                )

    # ── 4. Axiom evidence must be explicitly flagged ──────────────────────────
    for n in nodes:
        evidence = (n.get("evidence") or "").lower()
        if "axiom" in evidence:
            if not n.get("mathlib_gap") and not n.get("clay_gap"):
                errors.append(
                    f"[AXIOM]  Node {n['id']}: evidence contains 'axiom' "
                    f"but neither mathlib_gap nor clay_gap is set"
                )

    # ── Report ────────────────────────────────────────────────────────────────
    if errors:
        print(f"❌ REGISTRY ERRORS: {len(errors)}")
        for e in errors:
            print(f"   {e}")
        sys.exit(1)

    print(f"✅ {REPO_ROOT}/registry/nodes.yaml valid — 0 errors")
    print(f"   Nodes: {len(nodes)} | Critical-path nodes: {len(cp_nodes)}")


if __name__ == "__main__":
    main()
