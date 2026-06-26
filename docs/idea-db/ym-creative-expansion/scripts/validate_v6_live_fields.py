#!/usr/bin/env python3
import json, sqlite3, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
errors=[]
for rel in ['data/batch006_live_field_map.v6.json','data/raw_source_field_dag.v6.json','live_field_control/RAW_SOURCE_FIELD_DAG.md','live_field_control/ANTI_BACKFILL_AUDIT.md']:
    if not (ROOT/rel).exists(): errors.append(f'missing {rel}')
fields=json.loads((ROOT/'data/batch006_live_field_map.v6.json').read_text(encoding='utf-8'))['fields']
if len(fields) < 10: errors.append(f'expected at least 10 live fields, found {len(fields)}')
for f in fields:
    for k in ['rank','field','proof_card','contract','lean_targets','source_keys','blocker']:
        if k not in f: errors.append(f"field {f.get('field')} missing {k}")
contracts=list((ROOT/'mission_contracts').glob('OC_*.json'))
if len(contracts) < 30: errors.append(f'expected at least 30 mission contracts, found {len(contracts)}')
con=sqlite3.connect(ROOT/'data/ym_formula_expansion.sqlite')
db_count=con.execute('select count(*) from derived_cards').fetchone()[0]
mc_count=con.execute('select count(*) from mission_contracts').fetchone()[0]
lf_count=con.execute('select count(*) from live_fields').fetchone()[0]
if db_count < 105: errors.append(f'expected at least 105 derived cards in sqlite, found {db_count}')
if mc_count < 30: errors.append(f'expected at least 30 mission contracts in sqlite, found {mc_count}')
if lf_count < 10: errors.append(f'expected at least 10 live fields in sqlite, found {lf_count}')
if errors:
    print('\n'.join(errors)); sys.exit(1)
print(f'PASS: {db_count} cards, {mc_count} contracts, {lf_count} live fields; v6 live-field harness valid')
