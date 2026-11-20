from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from math import comb, prod
from pathlib import Path
from zipfile import ZipFile
import hashlib, json

def check(m, n, numerators, den):
    # Integer weights keep every enumerated probability exact.
    group = {}
    for u in product(range(n), repeat=m):
        group.setdefault(sum(u), []).append(u)
    scores = {s: F(comb(m+s-1, m-1), len(us)) for s, us in group.items()}
    targets = [ks for ks in product(range(n+1), repeat=m) if sum(ks) >= m]
    count = 0
    over, equal_off = [], []
    for a in combinations_with_replacement(numerators, m):
        observed = [[p*(den-p)**u*den**(n-1-u) for u in range(n)] for p in a]
        full = [[comb(n,k)*p**k*(den-p)**(n-k) for k in range(n+1)] for p in a]
        mean = sum(scores[s]*sum(prod(observed[i][v] for i,v in enumerate(u)) for u in us) for s,us in group.items())
        target = sum(prod(full[i][k] for i,k in enumerate(ks)) for ks in targets)
        delta = (target-mean)/den**(m*n)
        if len(set(a)) == 1:
            assert delta == 0
        if m==2:
            small, big = (F(p,den) for p in a)
            x,y = 1-small,1-big
            formula = sum((d+1)*(big**2*x**n*y**d+small**2*x**d*y**n
                -F(2,n-1-d)*small*big*sum(x**u*y**(n+d-u) for u in range(d+1,n))) for d in range(n-1))
            assert delta == formula and (delta>0)==(small!=big and n>1)
        if delta<0: over.append([a,str(delta)])
        if not delta and len(set(a))>1: equal_off.append(a)
        count+=1
    return dict(batches=m,cap=n,denominator=den,cases=count,overestimates=over,off_diagonal_ties=equal_off)

def main():
    rows=[check(2,n,range(9),8) for n in range(1,11)]
    rows.extend(check(m,n,range(5),4) for m,n in [(3,3),(3,4),(3,5),(4,3),(4,4)])
    output=Path('/content/archive.zip')
    with ZipFile(output,'w') as z:
        z.writestr('depth.json',json.dumps(rows))
    print('archive_sha256',hashlib.sha256(output.read_bytes()).hexdigest())

if __name__=='__main__': main()
