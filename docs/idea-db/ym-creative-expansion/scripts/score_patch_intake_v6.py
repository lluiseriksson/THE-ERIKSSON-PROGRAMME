#!/usr/bin/env python3
import argparse, json, sys
from pathlib import Path

def main():
    ap=argparse.ArgumentParser(description='v6 patch score with live-field/backfill penalties')
    ap.add_argument('intake')
    args=ap.parse_args()
    obj=json.loads(Path(args.intake).read_text(encoding='utf-8'))
    score = 10*len(obj.get('removed_fields',[])) + 8*len(obj.get('theorem_checked_promotions',[])) + 6*len(obj.get('source_promotions',[])) + 4*len(obj.get('toy_theorems',[]))
    score -= 8*len(obj.get('new_downstream_consumers',[]))
    score -= 6*len(obj.get('new_opaque_props',[]))
    score -= 15*len(obj.get('downstream_backfill_claims',[]))
    score -= 12*len(obj.get('monolithic_rawsource_claims',[]))
    hard_fail = bool(obj.get('core_import_violations') or obj.get('ocr_constant_uses') or obj.get('tautological_admissible_defs'))
    accept = score >= 10 and (obj.get('removed_fields') or obj.get('source_promotions') or obj.get('theorem_checked_promotions')) and not hard_fail
    print(json.dumps({'score':score,'accept':bool(accept),'hard_fail':hard_fail}, indent=2))
    if not accept: sys.exit(2)
if __name__=='__main__': main()
