#!/usr/bin/env python3
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
errors = []
required = {"id","proof_card","rank","mission","allowed_source_keys","target_shape","minimal_success","reject_if","expected_changed_paths","evidence_required"}
ids = set()
for p in sorted((ROOT/"mission_contracts").glob("OC_*.json")):
    obj = json.loads(p.read_text(encoding="utf-8"))
    miss = required - obj.keys()
    if miss: errors.append(f"{p.name} missing {sorted(miss)}")
    if obj.get("id") in ids: errors.append(f"duplicate id {obj.get('id')}")
    ids.add(obj.get("id"))
    if not obj.get("allowed_source_keys"): errors.append(f"{p.name} has no allowed source keys")
    if not obj.get("reject_if"): errors.append(f"{p.name} has no reject_if guardrails")
if errors:
    print("\n".join(errors)); sys.exit(1)
print(f"PASS: {len(ids)} mission contracts valid")
