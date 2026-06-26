#!/usr/bin/env python3
"""Render the v5 hypothesis-burndown vector."""
from __future__ import annotations
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main() -> int:
    p=ROOT/'data/hypothesis_burndown_vector.v5.json'
    obj=json.loads(p.read_text(encoding='utf-8'))
    print('| Field | Mission | Status | Weight |')
    print('|---|---|---:|---:|')
    total=0
    for row in obj['unresolved_vector']:
        total += int(row.get('weight',0)) if row.get('status') == 'open' else 0
        print(f"| `{row['id']}` | `{row['mission']}` | {row['status']} | {row['weight']} |")
    print(f"\nOpen weighted debt: {total}")
    return 0
if __name__ == '__main__':
    raise SystemExit(main())
