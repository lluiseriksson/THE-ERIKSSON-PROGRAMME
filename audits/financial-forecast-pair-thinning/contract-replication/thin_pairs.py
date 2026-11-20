"""Finite-panel contrasts from Aluguvelly (FinNLP 2026), Tables 3 and 10."""
from fractions import Fraction as F
from itertools import combinations,product
import json
def avg(a):return sum(a,F(0))/len(a)
def loss(z,y):return (z-y)**2
def verify(p,y):
    g=[avg(p[i:i+2]) for i in (0,2,4)];mean=avg(g)
    B=avg([(v-mean)**2 for v in g]);W=avg([(v-g[i//2])**2 for i,v in enumerate(p)])
    for same in (False, True):
        actual=avg([loss((p[i]+p[j])/2,y) for i,j in combinations(range(6),2) if (i//2==j//2)==same])
        expected=loss(mean,y)+(B if same else B/4+W/2)
        if actual!=expected:raise ValueError((p,y,same))
def ranges(e,b,w):
    # Relax the joint rounding constraints. Signs and threshold enclosures remain valid.
    triples=product(*[(F(x)-F(1,2*10**places),F(x)+F(1,2*10**places)) for x,places in [(e,5),(b,4),(w,4)]])
    vals=[]
    for E,B,W in triples:
        same=E+B;diff=E+B/4+W/2
        if same<=diff:raise ValueError('Slope sign')
        vals.append((same,diff,-diff/(same-diff)))
    return {k:[str(min(row[i] for row in vals)),str(max(row[i] for row in vals))] for i,k in enumerate(['same','distinct','zero'])}
if __name__=='__main__':
    checks=0
    for row in product((F(0),F(1,2),F(1)),repeat=6):
        for y in (0,1):verify(row,y);checks+=2
    data={'GPT-4.1-mini':['-0.00486','0.0091','0.0002'],'Qwen3-30B':['-0.01101','0.0064','0.0000'],'OLMo-3.1-32B':['-0.00418','0.0073','0.0001']}
    print(json.dumps({'enumerated_identities':checks,'source':'https://aclanthology.org/2026.finnlp-1.30/','sample':609,'effects':data,'enclosures':{k:ranges(*v) for k,v in data.items()}},indent=2))