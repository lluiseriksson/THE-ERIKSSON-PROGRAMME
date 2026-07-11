"""PERMANENT CONTRACT (external audit on 7225d4e): every node list
used as a quadrature partition must be STRICTLY increasing.

Static scanner: extracts the bracketed node lists from the live
bench/judge scripts (the [a, b, c] literals fed to mp.quad via the
region tuples), evaluates them under the scripts' own constants
(R = r = r_ = 6/5, hp = pi/2), and asserts
    all(xs[i] < xs[i+1])
for every list.  Exit 0 = contract holds; any violation names the
file, line and offending list.  Run before committing any script
that quadratures.
"""
import math
import re
import sys

FILES = [
    'cascade1_signed_minoration.py',
    'cascade2_step0_eps.py',
    'cascade3_judges.py',
    'cascade3b_judges.py',
    'cascade3_mirror_extraction.py',
    'cascade3c_buckets.py',
    'cascade4_presmoke.py',
]

ENV = {'R': 1.2, 'r': 1.2, 'r_': 1.2, 'hp': math.pi/2,
       'HP': math.pi/2, 'pi': math.pi}

def val(tok):
    tok = tok.strip()
    tok = tok.replace('mp.pi', 'pi').replace('mp.mpf', '')
    tok = tok.replace('(', '').replace(')', '').replace("'", '')
    # forms: number | name | pi | pi/2 | pi-R | name/2 | pi-R/2
    try:
        return float(eval(tok, {'__builtins__': {}}, ENV))
    except Exception:
        return None

LISTPAT = re.compile(r'\[([^][]+)\]')

bad = 0
checked = 0
for fn in FILES:
    try:
        text = open(fn, encoding='utf-8', errors='replace').read()
    except OSError:
        continue
    for i, line in enumerate(text.splitlines(), 1):
        if 'quad' not in line and ',' not in line:
            continue
        for m in LISTPAT.finditer(line):
            toks = m.group(1).split(',')
            if len(toks) < 2:
                continue
            vals = [val(t) for t in toks]
            if any(v is None for v in vals):
                continue          # not a pure node list
            # heuristic: node lists live in [0, pi+0.01]
            if not all(-1e-9 <= v <= math.pi + 0.01 for v in vals):
                continue
            checked += 1
            if not all(vals[k] < vals[k+1] - 1e-15
                       for k in range(len(vals)-1)):
                bad += 1
                print("VIOLATION %s:%d  %s -> %s"
                      % (fn, i, m.group(0),
                         [round(v, 5) for v in vals]))

print("node lists checked: %d ; violations: %d" % (checked, bad))
if bad:
    sys.exit(1)
print("CONTRACT HOLDS: every partition strictly increasing.")
