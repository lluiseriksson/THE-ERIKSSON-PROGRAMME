import json
from fractions import Fraction as Q
from itertools import product
from scipy.optimize import linprog
from tasknet_bounds import solve, ROWS

def need(value,reason):
    if not value:raise ValueError(reason)

def audit(row):
    n,e,et,r,rt=row
    als=solve(row);expected={tuple(t['counts']):t for t in als['tables']}
    seen=set();runs=0
    for i,j in product(range(n+1),repeat=2):
        if abs(200*i-2*e*n)>n or abs(200*j-2*r*n)>n:continue
        for k in range(max(0,i+j-n),min(i,j)+1):
            c=(k,i-k,j-k,n-i-j+k);check=[]
            for objective in (1,-1):
                fit=linprog([objective,0,0,0],A_eq=[[1,1,1,1]],b_eq=[1],
                            A_ub=[[1,1,0,0],[-1,-1,0,0],[1,0,1,0],[-1,0,-1,0]],
                            b_ub=[(et+.5)/100,-(et-.5)/100,(rt+.5)/100,-(rt-.5)/100],
                            bounds=[(0,None if count else 0) for count in c],method='highs')
                runs+=1
                if fit.success:check.append(fit.x[0])
                else:need(fit.status==2,'unexpected LP status')
            if not check:
                need(c not in expected,'spurious support');continue
            need(len(check)==2 and c in expected,'mismatched support');seen.add(c)
            for idx,key in enumerate(('lower','upper')):
                v=expected[c][key]
                need(abs(check[idx]-float(v[0]))<1e-8,'wrong LP bound')
                need(sum(v)==1 and all(y>=0 and (count or y==0) for count,y in zip(c,v)),'bad weights')
                need(abs(200*(v[0]+v[1])-2*et)<=1 and abs(200*(v[0]+v[2])-2*rt)<=1,'bad marginals')
    need(seen==set(expected),'missing tables')
    return runs

if __name__=='__main__':
    audits={k:audit(v) for k,v in ROWS.items()}
    base=solve(ROWS['Software Developers'])
    need(base['lower'][0]==Q(71,550) and base['upper'][0]==Q(57,200),'published control')
    gamma,c,w=base['critical_relative_time_error'];t=Q(c[0],sum(c))
    need(gamma==Q(162,91) and w[0]/(w[0]+gamma*(1-w[0]))==t,'breakdown witness')
    print(json.dumps(dict(lp_runs=audits,sharp_control=True,threshold=str(gamma)),indent=2))