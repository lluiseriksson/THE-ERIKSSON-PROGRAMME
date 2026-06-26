#!/usr/bin/env python3
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
    data=json.loads((ROOT/'data/batch006_live_field_map.v6.json').read_text(encoding='utf-8'))
    print('# Batch-006 field burndown\n')
    print('| Rank | Field | Contract | Blocker |')
    print('|---:|---|---|---|')
    for f in data['fields']:
        print(f"| {f['rank']} | `{f['field']}` | `{f['contract']}` | {f['blocker']} |")
if __name__=='__main__': main()
