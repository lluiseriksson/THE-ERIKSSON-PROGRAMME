"""Construct finite populations sharing the published ingredient means."""
from fractions import Fraction as Q
import json
base=[[Q(x) for x in row] for row in [('3.04','2.97','50.46'),('4.11','1.56','342.45'),('4.95','3.00','22.82')]]
threshold=[Q(3),Q('2.2'),Q(160)]
recipe=[Q(x) for x in ('24.50','41.83','33.65')]
cases=[]
for closure in range(3):
    c=recipe.copy();c[closure]+=Q('.02')
    # Two interpretations of the printed ingredient weights. Every shop has the same
    # moisture for a given grain, so pooling equal as-is masses preserves the dry means.
    dry=[v*(1-Q(m)/100) for v,m in zip(c,['8.65','11.36','9.12'])]
    for basis,p in [('dry',c),('as_weighed',dry)]:
        p=[v/sum(p) for v in p]
        level=[sum(w*g[j] for w,g in zip(p,base)) for j in range(3)]
        assert all(v>=t for v,t in zip(level,threshold))
        for k in range(10):
            if k==0:
                # Two disjoint failure groups. Each nutrient-specific shift has zero mean.
                changes=[(Q(0),Q('.4'),Q(-12))]*4+[(Q(0),Q('-.32'),Q('9.6'))]*5
            elif k==9:changes=[(Q(0),Q(0),Q(0))]*9
            else:changes=[(Q(0),Q(0),12*Q(9-k,k))]*k+[(Q(0),Q(0),Q(-12))]*(9-k)
            assert all(sum(s[j] for s in changes)==0 for j in range(3))
            assert all(g[j]+s[j]>=0 for g in base for s in changes for j in range(3))
            passing=[all(v+d>=t for v,d,t in zip(level,s,threshold)) for s in changes]
            assert sum(passing)==k
            cases.append(dict(closure=closure,basis=basis,passing=k,pooled=[str(x) for x in level]))
print(json.dumps(dict(order=['iron','zinc','calcium'],population_size=9,checks=len(cases),cases=cases,scope='Constructed populations for an additive same-outlet recipe, with the same three pooled ingredient assay vectors. No inferred retail frequencies or distribution.')))