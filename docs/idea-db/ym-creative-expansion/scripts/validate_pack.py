#!/usr/bin/env python3
import json, sqlite3, sys
from pathlib import Path
root = Path(__file__).resolve().parents[1]
errors = []
ids = set()
for n,line in enumerate((root/'formulas/derived_formula_cards.jsonl').read_text(encoding='utf-8').splitlines(),1):
    if not line.strip():
        continue
    obj = json.loads(line)
    if obj['id'] in ids:
        errors.append(f'duplicate card id {obj["id"]}')
    ids.add(obj['id'])
    for k in ['id','title','status','provenance','formula_ascii','why_it_matters','proof_route','blockers','risk']:
        if k not in obj:
            errors.append(f'missing {k} in line {n}')
con = sqlite3.connect(root/'data/ym_formula_expansion.sqlite')
db_ids = {r[0] for r in con.execute('select id from derived_cards')}
missing = ids - db_ids
if missing:
    errors.append('cards missing from sqlite: '+', '.join(sorted(missing)))
contract_ids = {r[0] for r in con.execute('select id from mission_contracts')} if con.execute("select name from sqlite_master where type='table' and name='mission_contracts'").fetchone() else set()
if len(contract_ids) < 9:
    errors.append(f'expected at least 9 mission contracts in sqlite, found {len(contract_ids)}')
for rel in [
    'rankings/BUILDER_PRIORITY.md',
    'rankings/BUILDER_PRIORITY_v3.md',
    'rankings/BUILDER_PRIORITY_v4.md',
    'builders/CONSTRUCTOR_PLAYBOOK_v2.es.md',
    'builders/CONSTRUCTOR_PLAYBOOK_v3.es.md',
    'falsification/NEGATIVE_TESTS.md',
    'falsification/NO_NEW_CONSUMERS_CHECK.md',
    'data/repo_update_scan.v3.json',
    'data/repo_update_scan.v4.json',
    'data/batch003_hypothesis_removal_queue.v3.json',
    'data/hypothesis_burndown_vector.v4.json',
    'post_integration/REPO_UPDATE_BRIEF.md',
    'ops/AGENT_MISSION_CONTROL_v4.md',
    'ops/PATCH_REVIEW_RUBRIC.md',
    'mission_contracts/README.md',
    'schemas/mission_contract.schema.json',
]:
    if not (root/rel).exists():
        errors.append(f'missing {rel}')
cards = list((root/'proof_obligation_cards').glob('PO_*.md')) if (root/'proof_obligation_cards').exists() else []
if len(cards) < 12:
    errors.append(f'expected at least 12 proof obligation cards, found {len(cards)}')
contracts = list((root/'mission_contracts').glob('OC_*.json')) if (root/'mission_contracts').exists() else []
if len(contracts) < 9:
    errors.append(f'expected at least 9 mission contracts, found {len(contracts)}')
if errors:
    print('\n'.join(errors))
    sys.exit(1)
print(f'PASS: {len(ids)} formula cards indexed; {len(contracts)} mission contracts; v4 mission-control pack structure valid')
