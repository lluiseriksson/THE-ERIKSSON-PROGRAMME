#!/usr/bin/env python3
"""List mission contracts and their ranks."""
from __future__ import annotations
import json, argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--ranked', action='store_true')
    args = ap.parse_args()
    rows=[]
    for p in sorted((ROOT/'mission_contracts').glob('OC_*.json')):
        obj=json.loads(p.read_text(encoding='utf-8'))
        rows.append((int(obj.get('rank',999)), obj.get('id',p.stem), obj.get('proof_card',''), obj.get('mission','')))
    rows.sort()
    for rank, cid, card, mission in rows:
        print(f"{rank:>3}  {cid}\n     card: {card}\n     mission: {mission}\n")
    return 0
if __name__ == '__main__':
    raise SystemExit(main())
