"""Independent vertex enumeration for the conditional portfolio-rounding supplement."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
from scipy.optimize import linprog

data=json.loads(Path('car-cert.json').read_text())['specs']
out={}
for name, spec in data.items():
    years=[list(map(F,spec[y])) for y in ['initial','final']]
    reported=list(map(F,spec['reported']))
    answers={}
    for sign in [-1,1]:
        lowest=None
        for heavy in combinations(range(8),4):
            w=[F(1,5) if j in heavy else F(1,20) for j in range(8)]
            objectives=[w,[sign*t for t in w]]
            total=F()
            for car,p,obj in zip(years,reported,objectives):
                d=F(1,200)
                a=8*(p-d)-sum(car);b=8*(p+d)-sum(car)
                lower=-8*d
                upper=8*d
                if max(lower,a)>min(upper,b):raise ValueError('Infeasible event')
                # HiGHS optimizes over the eight residuals subject to both sum bounds.
                sol=linprog(list(map(float,obj)),A_ub=[[1]*8,[-1]*8],b_ub=[float(b),float(-a)],bounds=(-float(d),float(d)),method='highs')
                if not sol.success:raise RuntimeError(sol.message)
                # Exact primal minimizer verified against lower floating LP optimum.
                positive=obj[0]>0
                errs=[-d if positive else d for i in w]
                need=max(F(),a+8*d if positive else 8*d-b)
                for j in sorted(range(8),key=w.__getitem__):
                    part=min(2*d,need);need-=part
                    errs[j]+=part if positive else -part
                exact=sum(x*y for x,y in zip(errs,obj))
                if need or not a<=sum(errs)<=b or abs(float(exact)-sol.fun)>1e-9:raise ValueError('LP mismatch')
                total+=sum(x*y for x,y in zip(car,obj))+exact
            if lowest is None or total<lowest:lowest=total
        answers['difference' if sign==-1 else 'sum']=str(lowest)
    out[name]=answers
expected={'market':{'difference':str(F('0.0755')),'sum':str(F('1.4855'))},'market_smh':{'difference':str(F('0.229')),'sum':str(F('1.6375'))}}
if out!=expected:raise ValueError((out,expected))
print(json.dumps(dict(minima=out,vertices_per_form=70,independent_linear_programs=560,assumption='Equal-weight portfolio equals the mean of issuer CARs before rounding.')))
