"""Reproduce the rank and partial-credit sensitivities from the original publisher map."""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from urllib.request import urlopen

MAP = 'https://ai-values-map.vercel.app/assets/index-CRWa8htl.js'
SHA = 'd48d828a73fa89381033695d2026d39a4bc52aaadf522407f5c7a08b1b42c8fa'
LEADERS = {'CAN', 'JPN'}

def records(raw, year):
    marker = f'title:"Artificial Intelligence and Democratic Values {year}"'
    assert raw.count(marker) == 1
    prefix, payload = raw.split(marker)[1].split("JSON.parse('", 1)
    assert 'scoringSystem:{Y:1,P:.5,N:0}' in prefix
    rows, end = json.JSONDecoder().raw_decode(payload)
    assert payload[end:end+2] == "')"
    scores = {}
    for row in rows:
        doubled = tuple({'Y': 2, 'P': 1, 'N': 0}[row['questions'][f'Q{i}']] for i in range(1,13))
        assert sum(doubled) == 2 * row['score']
        assert row['iso'] not in scores
        scores[row['iso']] = doubled
    assert scores['CAN'] == scores['JPN']
    assert {x for x,v in scores.items() if sum(v)==max(map(sum,scores.values()))} == LEADERS
    return scores

def entry(leader, outsiders):
    bounds = {}
    for country, vector in outsiders.items():
        deltas = [v-l for v,l in zip(vector,leader)]
        positive = sum(max(d,0) for d in deltas)
        loss = -sum(min(d,0) for d in deltas)
        if positive:
            bounds[country] = max(Fraction(1), Fraction(loss,positive))
        elif loss == 0:
            bounds[country] = Fraction(1)
    if not bounds:
        return {'radius':None, 'boundary':[], 'unreachable':len(outsiders)}
    radius = min(bounds.values())
    boundary = sorted(key for key in bounds if bounds[key]==radius)
    for key in boundary:
        weights = [radius if v>l else 1 for v,l in zip(outsiders[key],leader)]
        dot = lambda vec: sum(w*v for w,v in zip(weights,vec))
        assert dot(outsiders[key]) >= dot(leader)
        assert dot(outsiders[key]) == max(dot(vec) for vec in outsiders.values())
    return {'radius':str(radius), 'boundary':boundary, 'unreachable':len(outsiders)-len(bounds)}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--bundle',type=Path,help='previously saved publisher JavaScript; read as data only')
    args=ap.parse_args()
    if args.bundle:
        raw=args.bundle.read_bytes()
    else:
        with urlopen(MAP,timeout=60) as response:
            raw=response.read()
    if hashlib.sha256(raw).hexdigest()!=SHA:raise ValueError('Source changed')
    editions={y:records(raw.decode(),y) for y in (2025,2026)}
    common=editions[2025].keys() & editions[2026].keys()
    out={'common':len(common),'combinations':{},'editions':{}}
    for year, data in editions.items():
        outs={k:v for k,v in data.items() if k not in LEADERS}
        out['editions'][year]={'countries':len(data),**entry(data['CAN'],outs)}
        for ly,leaders in editions.items():
            out['combinations'][f'{ly}-{year}']=entry(leaders['CAN'],{k:outs[k] for k in common-LEADERS})
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':main()
