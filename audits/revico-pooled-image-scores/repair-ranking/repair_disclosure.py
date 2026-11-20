from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import json, subprocess
rows=[r for r in json.loads(Path('tables.json').read_bytes())['S3.T1'] if r['section']=='vision']
targets=[[int(10*F(row['values'][k])) for k in (0,1,2,6,7,8)] for row in rows]
subprocess.run(['g++','-std=c++17','-O2','repair_assignments.cpp','-o','assignments'],check=True)
lines=subprocess.check_output(['./assignments'],input=''.join(' '.join(map(str,row))+'\n' for row in targets).encode()).decode().splitlines()
names=['Tzh','Ten','Czh','Cen','FPzh','FPen','Tpool','Cpool','FPpool']
tests=[(i,) for i in range(9)]+list(combinations(range(9),2))
summary={','.join(names[i] for i in indices):dict(identified=[],counterexample=None) for indices in tests}
data=[];totals={}
for line in lines:
    if not line.startswith('END '):
        t,u,c,d,x,y=map(int,line.split())
        g=gcd(c+d,t+u)
        data.append(((t,u,c,d,x,y,t+u,c+d,x+y),((c+d)//g,(t+u)//g)))
        continue
    model=rows[len(totals)]['model']
    n=int(line.split()[1])
    if n!=len(data):raise ValueError(model)
    totals[model]=n
    for indices,case in zip(tests,summary.values(),strict=True):
        seen={}
        for i,(w,ratio) in enumerate(data):
            key=tuple(w[j] for j in indices);prior=seen.setdefault(key,i)
            prev,other=data[prior]
            if other!=ratio:
                if case['counterexample'] is None:case['counterexample']=dict(model=model,fields=list(key),w1=prev[:6],w2=w[:6],ratio1=other,ratio2=ratio)
                break
        else:case['identified'].append(model)
    data=[]
if len(totals)!=20 or data:raise ValueError('Incomplete enumeration')
print(json.dumps(dict(totals=totals,disclosures=summary)))