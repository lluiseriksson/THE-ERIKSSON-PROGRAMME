from fractions import Fraction as F
from pathlib import Path
import subprocess,json
tables=json.loads(Path('tables.json').read_bytes())
rows=[r for r in tables['S3.T1'] if r['section']=='vision']
names=[r['model'] for r in rows];target=[[int(F(r['values'][k])*10) for k in [0,1,2,6,7,8]] for r in rows]
subprocess.run(['g++','-O2','-std=c++17','lang_harmonic.cpp','-o','lang_counts'],check=True)
out=subprocess.check_output(['./lang_counts'],input=''.join(' '.join(map(str,row))+'\n' for row in target).encode()).decode().splitlines()
if len(out)!=len(rows):raise ValueError('Missing rows')
result={};eps=F(1,10**8)
for name,row,line in zip(names,target,out):
    hits,t,u,c,d,x,y=map(int,line.split()); witness=None
    if hits:
        vals=[(t,t+x,u,u+y),(t,376,u,266),(2*t,376+t+x,2*u,266+u+y),(c,c+x,d,d+y),(c,376,d,266),(2*c,376+c+x,2*d,266+d+y)]
        pr=[500*(a/(b+eps)+c1/(d1+eps)) for a,b,c1,d1 in vals]
        for k in [0,3]:pr[k+2]=2*pr[k]*pr[k+1]/(pr[k]+pr[k+1])
        if not all(abs(value-v)<=F(1,2) for value,v in zip(pr,row)):raise ValueError('Numerical nomination failed exact replay')
        witness=[t,u,c,d,x,y]
    result[name]=dict(candidate_hits=hits,exact_witness=witness)
print(json.dumps(result))
