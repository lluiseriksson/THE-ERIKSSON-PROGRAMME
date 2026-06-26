#!/usr/bin/env python3
"""Validate the v5 execution harness files."""
from __future__ import annotations
import json, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def fail(msg: str) -> None:
    print(f'FAIL: {msg}')
    raise SystemExit(1)

def main() -> int:
    contracts=[]
    for p in sorted((ROOT/'mission_contracts').glob('OC_*.json')):
        obj=json.loads(p.read_text(encoding='utf-8'))
        for field in ['id','rank','proof_card','mission','allowed_source_keys','target_shape','minimal_success','reject_if']:
            if field not in obj:
                fail(f'{p.name} missing {field}')
        contracts.append(obj['id'])
    if len(contracts) < 15:
        fail(f'expected at least 15 contracts, found {len(contracts)}')
    for name in ['PATCH_INTAKE_SCHEMA.v5.json','INTAKE_TEMPLATE_v5.json']:
        if not (ROOT/'patch_intake'/name).exists():
            fail(f'missing patch_intake/{name}')
    for script in ['mission_board.py','generate_patch_intake.py','score_patch_intake.py','render_hypothesis_burndown.py']:
        if not (ROOT/'scripts'/script).exists():
            fail(f'missing script {script}')
    print(f'PASS: {len(contracts)} mission contracts and v5 harness files validated')
    return 0
if __name__ == '__main__':
    raise SystemExit(main())
