#!/usr/bin/env python3
import argparse, sqlite3, pathlib, json, sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

DB = pathlib.Path(__file__).resolve().parents[1] / 'data' / 'ym_formula_expansion.sqlite'

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--list-cards', action='store_true')
    p.add_argument('--list-atoms', action='store_true')
    p.add_argument('--queue', action='store_true')
    p.add_argument('--search')
    args = p.parse_args()
    con = sqlite3.connect(DB)
    con.row_factory = sqlite3.Row
    cur = con.cursor()
    if args.list_cards:
        for r in cur.execute('select id,status,title from derived_cards order by id'):
            print(f"{r['id']} [{r['status']}] {r['title']}")
    elif args.list_atoms:
        for r in cur.execute('select id,status,summary from source_atoms order by id'):
            print(f"{r['id']} [{r['status']}] {r['summary']}")
    elif args.queue:
        for r in cur.execute('select rank,task,payoff,risk from handoff_queue order by rank'):
            print(f"#{r['rank']} {r['task']} | payoff={r['payoff']} | risk={r['risk']}")
    elif args.search:
        q = f"%{args.search.lower()}%"
        print('SOURCE ATOMS')
        for r in cur.execute('select id,status,summary from source_atoms where lower(id)||lower(summary)||lower(formula_ascii) like ? order by id', (q,)):
            print(f"- {r['id']} [{r['status']}] {r['summary']}")
        print('DERIVED CARDS')
        for r in cur.execute('select id,status,title from derived_cards where lower(id)||lower(title)||lower(formula_ascii)||lower(why_it_matters) like ? order by id', (q,)):
            print(f"- {r['id']} [{r['status']}] {r['title']}")
    else:
        p.print_help()

if __name__ == '__main__':
    main()


# v2 note: if you want campaign scores, run this small standalone query:
# python - <<'PY'
# import sqlite3
# con=sqlite3.connect('data/ym_formula_expansion.sqlite')
# for row in con.execute('select rank,campaign,payoff,risk,lean_nearness,recommended_next_action from campaign_scoreboard order by rank'):
#     print(row)
# PY
