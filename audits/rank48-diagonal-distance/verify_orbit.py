"""Certify a diagonal orbit optimum in Q(sqrt(discriminant)), on a pinned scheme."""
import hashlib
import json
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import sympy as sp

from urllib.request import urlopen
input_path=Path('scheme.json')
if not input_path.exists():
    location=json.loads(Path('sources.json').read_bytes())['files'][0]['url']
    with urlopen(location,timeout=25) as handle:
        payload=handle.read()
    if hashlib.sha256(payload).hexdigest()!='b82a3cef30dacb9ee08be73d13449123bb073716888a081d52bfae0a0205b4ee':
        raise ValueError('Scheme download differs')
    input_path.write_bytes(payload)
raw = Path("scheme.json").read_bytes()
if not (hashlib.sha256(raw).hexdigest() == "b82a3cef30dacb9ee08be73d13449123bb073716888a081d52bfae0a0205b4ee"): raise ValueError("Exact certificate check failed at line %s" % 19)
doc = json.loads(raw)
D = 4328**2 - 4*35*24584
K = sp.QQ.algebraic_field(sp.sqrt(D))
def q(x):
    return K.from_sympy(sp.Rational(x))
def expr(x):
    return K.to_sympy(x)
L = K.from_sympy((4328+sp.sqrt(D))/70)
old = list(map(F,doc["meta"]["row_scales"]))
if not (old == [1,F(1406919,427109),1,F(204129,422224)]): raise ValueError("Exact certificate check failed at line %s" % 29)
a = (7595*L-4968)/(2508*L-25320)
b = (1096*L+1472)/(2508*L-25320)
s = [v/q(t) for v,t in zip([K.one,a,K.one,b],old)]
if not (all(expr(v).is_positive for v in s)): raise ValueError("Exact certificate check failed at line %s" % 33)
terms = [defaultdict(F) for _ in range(16)]
def entries(matrix):
    return [(r,c,abs(F(x))) for r,row in enumerate(matrix) for c,x in enumerate(row) if F(x)]
for U,V,W in zip(doc["u"],doc["v"],doc["w"]):
    for i,k,w in entries(W):
        for r,c,u in entries(U):
            for f,h,v in entries(V):
                terms[4*i+k][(r,c,f,h,i,k)] += u*v*w
grad = []; exponents = []; values = []
for table in terms:
    value = K.zero
    g = [K.zero]*12
    expo = set()
    for (r,c,f,h,i,k),coef in table.items():
        ev = [0]*12
        for ix,delta in [(r,1),(4+c,-1),(4+f,1),(8+h,-1),(i,-1),(8+k,1)]:
            ev[ix] += delta
        coeff = q(coef)*s[r]/s[i]
        value += coeff
        for j,d in enumerate(ev):
            if d: g[j] += d*coeff
        expo.add(tuple(ev))
    values.append(value)
    grad.append(g)
    exponents.append(expo)
if not (values == [L]*16): raise ValueError("Exact certificate check failed at line %s" % 59)
support = [1,2,4,8,9,10,11,14,15]
rows = [[K.one]*len(support)+[K.one]]
rows.extend([[grad[i][j] for i in support]+[K.zero] for j in range(12)])
for col in range(len(support)):
    pivot = next(i for i in range(col,len(rows)) if rows[i][col])
    rows[col],rows[pivot] = rows[pivot],rows[col]
    norm = rows[col][col]
    rows[col] = [v/norm for v in rows[col]]
    for j,row in enumerate(rows):
        if j != col and row[col]:
            rows[j] = [v-row[col]*w for v,w in zip(row,rows[col])]
weights = [row[-1] for row in rows[:len(support)]]
if not (sum(weights,K.zero)==K.one and all(expr(v).is_positive for v in weights)): raise ValueError("Exact certificate check failed at line %s" % 72)
if not (all(sum((p*grad[i][j] for p,i in zip(weights,support)),K.zero)==K.zero for j in range(12))): raise ValueError("Exact certificate check failed at line %s" % 73)

masses=defaultdict(lambda:K.zero)
for p,iout in zip(weights,support):
    for (r,c,f,h,i,k),coef in terms[iout].items():
        ev=[0]*12
        for ix,delta in [(r,1),(4+c,-1),(4+f,1),(8+h,-1),(i,-1),(8+k,1)]:ev[ix]+=delta
        # Fix the last coordinate of each log basis at zero.
        key=tuple(ev[j] for j in (0,1,2,4,5,6,8,9,10))
        masses[key]+=p*q(coef)*s[r]/s[i]
pairs=[]
for key,plus in list(masses.items()):
    minus=masses.get(tuple(-t for t in key))
    if key<=tuple(-t for t in key) or minus is None:continue
    # Use floating point for selecting a convenient rational lower bound only.
    floor=int(1e6*min(float(expr(minus)),float(expr(plus))))-1
    if floor<=0:continue
    bound=sp.Rational(floor,10**6)
    if not (expr(minus-q(bound)).is_positive and expr(plus-q(bound)).is_positive): raise ValueError("Exact certificate check failed at line %s" % 91)
    pairs.append((key,bound))
H=sp.zeros(9)
for key,v in pairs:
    row=sp.Matrix(key);H+=v*(row*row.T)
lo=sp.Rational(0);hi=sp.Rational(128)
for step in range(14):
    mid=(lo+hi)/2
    if (H-mid*sp.eye(9)).is_positive_definite:lo=mid
    else:hi=mid
if not (lo>0): raise ValueError("Exact certificate check failed at line %s" % 101)
minor=[(H-lo*sp.eye(9))[:i,:i].det() for i in range(1,10)]
if not (all(x>0 for x in minor)): raise ValueError("Exact certificate check failed at line %s" % 103)
result=dict(paired_exponents=len(pairs),norm="nine log ratios relative to index 3",lower=str(lo),
    pairs=[[list(k),str(v)] for k,v in pairs],leading_minors=list(map(str,minor)),
    growth_at_optimum=str(expr(L)),output_weights=list(map(lambda x:str(expr(x)),weights)),
    support=support,relative_scaling=[str(expr(x)) for x in s])

if result!=json.loads(Path("modulus.json").read_bytes()): raise ValueError("Certificate differs")
print(json.dumps(dict(pairs=len(pairs),lower=str(lo),positive_minors=len(minor),balanced_outputs=len(values))))
