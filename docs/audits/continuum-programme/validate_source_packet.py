#!/usr/bin/env python3
"""Validate this desk's source packet with the repository's canonical schema code.

The packet is intentionally kept under docs/audits/continuum-programme because
the desk's write charter does not authorize edits to docs/source-db/catalogs.
This script loads scripts/source_db.py and calls the same validate_catalogs
function on the explicit audit packet.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PACKET = HERE / "continuum-os-source-packet.json"
SOURCE_DB = ROOT / "scripts" / "source_db.py"


def main() -> int:
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("repository_source_db", SOURCE_DB)
    if spec is None or spec.loader is None:
        print(f"FAIL: cannot load {SOURCE_DB}", file=sys.stderr)
        return 1
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)

    try:
        data = json.loads(PACKET.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"FAIL: cannot read packet: {exc}", file=sys.stderr)
        return 1

    record = module.CatalogRecord(path=PACKET, data=data)
    errors = module.validate_catalogs([record], root=ROOT)
    if errors:
        print("FAIL: source packet violates canonical catalog schema")
        for error in errors:
            print(f"  - {error}")
        return 1

    print("PASS: continuum-os-source-packet.json satisfies canonical catalog validation")
    print(f"sources={len(data.get('sources', {}))}")
    print(f"citations={len(data.get('citations', []))}")
    print(f"coverage={len(data.get('coverage', []))}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
