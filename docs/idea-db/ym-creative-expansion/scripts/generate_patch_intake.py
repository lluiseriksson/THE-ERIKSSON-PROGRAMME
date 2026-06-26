#!/usr/bin/env python3
"""Generate a patch-intake JSON skeleton from a mission contract."""
from __future__ import annotations
import json, argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main() -> int:
    ap=argparse.ArgumentParser()
    ap.add_argument('contract_id')
    args=ap.parse_args()
    path=ROOT/'mission_contracts'/f'{args.contract_id}.json'
    if not path.exists():
        raise SystemExit(f'unknown contract: {args.contract_id}')
    c=json.loads(path.read_text(encoding='utf-8'))
    obj={
      'contract_id': c['id'],
      'proof_card': c.get('proof_card',''),
      'source_keys_touched': c.get('allowed_source_keys',[]),
      'lean_targets_touched': [],
      'delta': {
        'removed_fields': 0,
        'source_promotions': 0,
        'theorem_checked_promotions': 0,
        'toy_theorems': 0,
        'new_consumers_without_removed_fields': 0,
        'new_opaque_props': 0,
        'core_import_violations': 0,
        'ocr_constant_uses': 0,
        'tautological_admissible_defs': 0,
      },
      'verification_evidence': {
        'lake_build_YangMillsCore': 'not_run',
        'oracle_check': 'not_run',
        'source_db_verify': 'not_run'
      },
      'removed_premises': [],
      'remaining_blockers': [],
      'notes': c.get('minimal_success','')
    }
    print(json.dumps(obj, indent=2, ensure_ascii=False, sort_keys=True))
    return 0
if __name__ == '__main__':
    raise SystemExit(main())
