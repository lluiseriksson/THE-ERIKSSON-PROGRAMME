"""Feasibility audit for the pooled, common-denominator interpretation."""
from fractions import Fraction as F
import json
from pathlib import Path
from math import ceil,floor
rows=[(r['model'],list(map(F,r['values']))) for r in json.loads(Path('tables.json').read_bytes())['S3.T1'] if r['section']=='vision']
# A conservative relaxation allows different stabilizers anywhere in [0,.001] for different cells.
tol=F(1,20);st=F(1,1000)
def possible(r,n):
    return range(ceil((r-tol)*n/100),floor((r+tol)*(n+st)/100)+1)
def compatible(k,den,r):
    return 100*k >= (r-tol)*den and 100*k <= (r+tol)*(den+st)
def audit(n,clean):
    answer={}
    for name,v in rows:
        pd,rd,fd,pc,rc,fc=[v[i] for i in (0,1,2,6,7,8)]
        sol=[]
        for t in possible(rd,n):
            for c in possible(rc,n):
                if not 0<=c<=t<=n:continue
                low=max(0,ceil(100*t/(pd+tol)-t-st),ceil(100*c/(pc+tol)-c-st))
                high=min(clean,floor(100*t/(pd-tol)-t),floor(100*c/(pc-tol)-c))
                for f in range(low,high+1):
                    if all(compatible(k,den,r) for k,den,r in [(t,t+f,pd),(c,c+f,pc),(2*t,n+t+f,fd),(2*c,n+c+f,fc)]):sol.append([t,c,f])
        answer[name]=sol
    return answer
at_figure=audit(642,587)
def matching(n):return sum(bool(possible(r,n)) for _,v in rows for r in (v[1],v[7]))
recall_counts={n:matching(n) for n in range(1,1230)}
all_ok=[n for n,k in recall_counts.items() if k==2*len(rows)]
feas={n:[k for k,v in audit(n,1229-n).items() if not v] for n in all_ok}
print(json.dumps(dict(total=1229,error_images=642,clean_images=587,epsilon_upper=str(st),rows=len(rows),
    figure_row_solutions=at_figure,figure_compatible_recall_cells=recall_counts[642],
    all_recalls_possible=all_ok,full_table_possible=[n for n,u in feas.items() if not u],
    nearest_recall_denominators=sorted(all_ok,key=lambda n:abs(n-642))[:5],
    best_fully_compatible_rows_among_recall_candidates=max([len(rows)-len(u) for u in feas.values()] or [0]),
    recalled_example={'model':rows[0][0],'recall':str(rows[0][1][1]),'candidates':list(possible(rows[0][1][1],642))})))
