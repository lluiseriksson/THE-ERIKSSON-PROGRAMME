#!/usr/bin/env python3
import argparse, json, sys
from pathlib import Path
FORBIDDEN = [
    'final lemma 3 proves hessian',
    'hsharp identity proves gaussian',
    'dimock scalar proves yang-mills covariance',
    'decay proves support',
    'rsc flow proves activity construction',
    'downstream bound discharges upstream',
]

def main():
    ap=argparse.ArgumentParser(description='Hard-fail common downstream backfill claims in a patch intake JSON')
    ap.add_argument('intake')
    args=ap.parse_args()
    obj=json.loads(Path(args.intake).read_text(encoding='utf-8'))
    text=json.dumps(obj, ensure_ascii=False).lower()
    hits=[x for x in FORBIDDEN if x in text]
    fields=obj.get('removed_fields',[])
    downstream=obj.get('downstream_evidence_used',[])
    if downstream and not obj.get('separate_upstream_source_theorems'):
        hits.append('downstream evidence without separate upstream source theorem')
    result={'accept_no_backfill': not hits, 'hits': hits, 'removed_fields': fields}
    print(json.dumps(result, indent=2, ensure_ascii=False))
    if hits: sys.exit(2)
if __name__=='__main__': main()
