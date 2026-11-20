"""Exact price intervals for pathwise, all-budget dominance."""
import itertools
from fractions import Fraction as F
from decimal import Decimal
from hashlib import sha256
from pathlib import Path
import json
import zipfile

def records(seq):
    scored = missing = 0
    best = None
    knots = []
    for v in seq:
        if v is None:
            missing += 1
            continue
        scored += 1
        if best is None or v > best:
            knots.append((v, scored, missing))
            best = v
    return knots

def interval(a, b):
    ar = records(a)
    lo, hi = F(0), F(1)
    constraints = []
    i = 0
    for target, s, f in records(b):
        while i < len(ar) and ar[i][0] < target:
            i += 1
        if i == len(ar):
            return None, constraints + [{"unreached":str(target)}]
        u, v = ar[i][1]-s, ar[i][2]-f
        constraints.append(dict(target=str(target), scored_difference=u, unscored_difference=v))
        if v == 0 and u > 0:
            return None, constraints
        if v > 0:
            hi = min(hi, F(-u,v))
        if v < 0:
            lo = max(lo, F(-u,v))
        if lo > hi:
            return None, constraints
    return [lo,hi], constraints

def affordable(seq, price, budget):
    cost = F(0)
    vals = []
    for value in seq:
        cost += price if value is None else 1
        if cost > budget:
            break
        if value is not None:
            vals.append(value)
    return max(vals, default=None)

def direct(a, b, price):
    times = {F(0)}
    for seq in [a,b]:
        cost = 0
        for v in seq:
            cost += price if v is None else 1
            times.add(cost)
    for t in times:
        x, y = affordable(a,price,t), affordable(b,price,t)
        if y is not None and (x is None or x < y):
            return False
    return True

def verify():
    seqs = list(itertools.product((None,0,1),repeat=3))
    roots = sorted({F(i,j) for j in range(1,4) for i in range(j+1)})
    prices = roots + [(a+b)/2 for a,b in zip(roots,roots[1:])]
    for a,b in itertools.product(seqs,repeat=2):
        iv,_ = interval(a,b)
        for p in prices:
            if bool(iv and iv[0] <= p <= iv[1]) != direct(a,b,p):
                raise ValueError((a,b,p,iv))
    a,b=[1,None,None,None,3,0],[0,None,None,2,0]
    for p,expect in [(F(0),1),(F(1,3),1),(F(2,5),-1),(F(1,2),-1),(F(3,5),1),(F(1),1)]:
        va,vb = affordable(a,p,3), affordable(b,p,3)
        if (va>vb)-(va<vb)!=expect:
            raise ValueError("Fixed-budget witness mismatch")
    return len(seqs)**2, len(prices)

def apply(data):
    table = {"resnet_l40s":"resnet","lr_synthetic":"lr","autoresearch_none":"linux","autoresearch_summary":"linux"}
    lookup = {(table[r["table7_row"]],r["seed"],r["arm"]):r["campaign_id"] for r in data["inputs"]}
    output = []
    for pair in data["pairs"]:
        a,b = pair["arms"]
        task, seed = pair["task"], pair["seed"]
        def seq(arm):
            xs=data["sequences"][lookup[task,seed,arm]]
            return [None if v is None else Decimal(v)*(-1 if task=="linux" else 1) for v in xs]
        for x,y in [(a,b),(b,a)]:
            iv, conditions=interval(seq(x),seq(y))
            output.append(dict(task=task,seed=seed,arms=[x,y],matched=pair["matched"],interval=iv,constraints=conditions))
    return output

def run(data, dest):
    cases,prices=verify()
    result=dict(validation=dict(ordered_pairs=cases,prices=prices),domains=apply(data))
    with zipfile.ZipFile(dest,"w",zipfile.ZIP_DEFLATED) as z:
        z.writestr("prices.json",json.dumps(result,default=str,indent=2)+"\n")
    print("archive_sha256",sha256(Path(dest).read_bytes()).hexdigest())
