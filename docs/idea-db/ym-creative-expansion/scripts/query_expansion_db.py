#!/usr/bin/env python3
import argparse, sqlite3, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
DB = ROOT/'data/ym_formula_expansion.sqlite'

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--list-cards', action='store_true')
    p.add_argument('--list-contracts', action='store_true')
    p.add_argument('--search')
    p.add_argument('--queue', action='store_true')
    args = p.parse_args()
    con = sqlite3.connect(DB)
    if args.list_cards:
        for row in con.execute('select id,title,status,risk from derived_cards order by id'):
            print(' | '.join(str(x) for x in row))
    elif args.list_contracts:
        for row in con.execute('select rank,id,proof_card,mission from mission_contracts order by rank'):
            print(f"{row[0]:>2} | {row[1]} | {row[2]} | {row[3]}")
    elif args.search:
        q = f"%{args.search}%"
        for row in con.execute('select id,title,formula_ascii from derived_cards where id like ? or title like ? or formula_ascii like ? order by id', (q,q,q)):
            print(f"## {row[0]} — {row[1]}\n{row[2]}\n")
        for row in con.execute('select id,proof_card,mission from mission_contracts where id like ? or proof_card like ? or mission like ? order by rank', (q,q,q)):
            print(f"## CONTRACT {row[0]} — {row[1]}\n{row[2]}\n")
    elif args.queue:
        path = ROOT/'data/hypothesis_burndown_vector.v4.json'
        print(path.read_text(encoding='utf-8'))
    else:
        p.print_help()
if __name__ == '__main__': main()
