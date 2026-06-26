#!/usr/bin/env python3
import json, sqlite3, sys
from pathlib import Path
root = Path(__file__).resolve().parents[1]
errors = []
# JSONL cards valid and IDs unique
ids = set()
for n,line in enumerate((root/'formulas/derived_formula_cards.jsonl').read_text(encoding='utf-8').splitlines(),1):
    if not line.strip(): continue
    obj = json.loads(line)
    if obj['id'] in ids: errors.append(f'duplicate card id {obj["id"]}')
    ids.add(obj['id'])
    for k in ['id','title','status','formula_ascii','risk']:
        if k not in obj: errors.append(f'missing {k} in line {n}')
# SQLite contains the same card IDs
con = sqlite3.connect(root/'data/ym_formula_expansion.sqlite')
db_ids = {r[0] for r in con.execute('select id from derived_cards')}
missing = ids - db_ids
if missing: errors.append('cards missing from sqlite: '+', '.join(sorted(missing)))
# Key files
for rel in ['rankings/BUILDER_PRIORITY.md','builders/CONSTRUCTOR_PLAYBOOK_v2.es.md','falsification/NEGATIVE_TESTS.md']:
    if not (root/rel).exists(): errors.append(f'missing {rel}')
if errors:
    print('\n'.join(errors))
    sys.exit(1)
print(f'PASS: {len(ids)} formula cards indexed; v2 pack structure valid')
