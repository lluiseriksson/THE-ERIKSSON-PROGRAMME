#!/usr/bin/env python3
import argparse, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main():
    ap=argparse.ArgumentParser(description='Compile a Batch-006 field prompt')
    ap.add_argument('field')
    args=ap.parse_args()
    data=json.loads((ROOT/'data/batch006_live_field_map.v6.json').read_text(encoding='utf-8'))
    matches=[f for f in data['fields'] if f['field']==args.field or f['contract']==args.field]
    if not matches: raise SystemExit(f'unknown field/contract: {args.field}')
    f=matches[0]
    print(f"# Batch-006 field mission: {f['field']}\n")
    print(f"Contract: `{f['contract']}`")
    print(f"Proof card: `{f['proof_card']}`\n")
    print('Source keys:')
    for k in f['source_keys']: print(f'- `{k}`')
    print('\nLean targets:')
    for k in f['lean_targets']: print(f'- `{k}`')
    print('\nBlocker:')
    print(f['blocker'])
    print('\nGuard: final H#/Lemma-3/downstream bounds cannot discharge upstream fields unless a separate source theorem is supplied.')
if __name__=='__main__': main()
