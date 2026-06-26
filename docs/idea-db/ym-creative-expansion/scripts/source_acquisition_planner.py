#!/usr/bin/env python3
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
    data=json.loads((ROOT/'data/batch006_live_field_map.v6.json').read_text(encoding='utf-8'))
    seen=[]
    for f in data['fields']:
        for k in f['source_keys']:
            if k not in seen: seen.append(k)
    print('# Batch-006 source acquisition plan\n')
    for k in seen:
        print(f'- `{k}`: locator/hash/artifact status must be checked before source promotion.')
if __name__=='__main__': main()
