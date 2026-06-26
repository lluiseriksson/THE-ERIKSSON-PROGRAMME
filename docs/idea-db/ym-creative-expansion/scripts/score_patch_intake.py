#!/usr/bin/env python3
"""Score a v5 patch-intake JSON."""
from __future__ import annotations
import json, argparse
from pathlib import Path

def score(d: dict) -> int:
    return (10*d.get('removed_fields',0)
        + 6*d.get('source_promotions',0)
        + 8*d.get('theorem_checked_promotions',0)
        + 4*d.get('toy_theorems',0)
        - 8*d.get('new_consumers_without_removed_fields',0)
        - 6*d.get('new_opaque_props',0)
        - 20*d.get('core_import_violations',0)
        - 12*d.get('ocr_constant_uses',0)
        - 12*d.get('tautological_admissible_defs',0))

def main() -> int:
    ap=argparse.ArgumentParser()
    ap.add_argument('intake')
    args=ap.parse_args()
    obj=json.loads(Path(args.intake).read_text(encoding='utf-8'))
    d=obj.get('delta',{})
    s=score(d)
    positive=sum(d.get(k,0) for k in ['removed_fields','source_promotions','theorem_checked_promotions','toy_theorems'])
    accepted = s >= 10 and positive >= 1 and d.get('core_import_violations',0)==0
    print(json.dumps({'score':s,'positive_delta':positive,'accepted':accepted}, indent=2))
    return 0 if accepted else 2
if __name__ == '__main__':
    raise SystemExit(main())
