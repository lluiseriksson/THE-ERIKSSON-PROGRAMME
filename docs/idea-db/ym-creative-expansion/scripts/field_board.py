#!/usr/bin/env python3
import argparse, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

def main():
    ap=argparse.ArgumentParser(description='Show Batch-006 live-field board')
    ap.add_argument('--order', action='store_true')
    ap.add_argument('--json', action='store_true')
    args=ap.parse_args()
    data=json.loads((ROOT/'data/batch006_live_field_map.v6.json').read_text(encoding='utf-8'))
    if args.json:
        print(json.dumps(data, indent=2, ensure_ascii=False)); return
    for f in sorted(data['fields'], key=lambda x:x['rank']):
        print(f"{f['rank']:02d}. {f['field']}  contract={f['contract']}")
        print(f"    blocker: {f['blocker']}")
        if args.order:
            print(f"    targets: {', '.join(f['lean_targets'])}")
if __name__=='__main__': main()
