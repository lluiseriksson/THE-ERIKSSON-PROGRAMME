"""Reporting-precision analysis using exact integer inequalities for 3--5 decimals."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import numpy as np
import hashlib,json
from zipfile import ZipFile,ZIP_DEFLATED

N=122
def scan(hits,fvals,mvals):
    p,q,r=np.array([(i,j,hits-i-j) for i in range(hits+1) for j in range(hits-i+1)],dtype=np.int64).T
    result={d:defaultdict(dict) for d in fvals}
    errs=N-hits
    for cut in combinations(range(errs+5),5):
        edge=(-1,)+cut+(errs+5,)
        a,b,c,d,e,f=(y-x-1 for x,y in zip(edge,edge[1:]))
        R0,R1,R2=p+a+b,q+c+d,r+e+f
        C0,C1,C2=p+c+e,q+a+f,r+b+d
        u,v,w=R0+C0,R1+C1,R2+C2
        Fnum=2*(R0*p*v*w+R1*q*u*w+R2*r*u*v)
        Fden=N*u*v*w
        m=N*hits-R0*C0-R1*C1-R2*C2
        z=(N*N-R0**2-R1**2-R2**2)*(N*N-C0**2-C1**2-C2**2)
        base=(R0>0)&(R0<=R1)&(R1<=R2)&(m>0)&(z>0)
        for dec,num in fvals.items():
            scale=10**dec; mv=mvals[dec]
            A=4*scale**2*m**2
            mask=base&(abs(2*scale*Fnum-2*num*Fden)<=Fden)&((2*mv-1)**2*z<=A)&(A<=(2*mv+1)**2*z)
            for j in np.flatnonzero(mask):
                row=(int(R0[j]),int(R1[j]),int(R2[j]))
                # The designated least-supported class is first; tied true supports admit both orders.
                result[dec][row].setdefault(int(p[j]),[[int(p[j]),a,b],[c,int(q[j]),d],[e,f,int(r[j])]])
    return result

def main():
    assert 4*10**10*N**4<2**63 and 2*10**5*N*(2*N)**3<2**63
    def digits(x):
        return {d:round(F(x)*10**d) for d in [3,4,5]}
    # Full published intervals lie strictly within the new rounding cells.
    for x in ['0.91079235','0.842682','0.906464389','0.827407']:
        h=F(1,2*10**len(x.split('.')[1]))
        for d,rd in digits(x).items():
            assert abs(F(x)-F(rd,10**d))+h<F(1,2*10**d)
    a=scan(112,digits('0.91079235'),digits('0.842682'))
    b=scan(111,digits('0.906464389'),digits('0.827407'))
    result={}
    for d in a:
        rows=sorted(set(a[d]) & set(b[d]))
        assert (3,58,61) in rows
        deltas={}; recall_pairs=set()
        for row in rows:
            for x,table in a[d][row].items():
                for y,btable in b[d][row].items():
                    delta=F(x-y,row[0]);recall_pairs.add((F(x,row[0]),F(y,row[0])))
                    deltas.setdefault(delta,dict(smote=table,borderline=btable))
        result[d]=dict(supports=len(rows),recall_pairs=len(recall_pairs),both_zero=recall_pairs=={(F(0),F(0))},
                       minimum=str(min(deltas)),maximum=str(max(deltas)),
                       min_witness=deltas[min(deltas)],max_witness=deltas[max(deltas)])
    path=Path('/content/archive.zip')
    with ZipFile(path,'w',ZIP_DEFLATED) as z:z.writestr('precision.json',json.dumps(result,indent=2))
    print('archive_sha256',hashlib.sha256(path.read_bytes()).hexdigest())
if __name__=='__main__': main()
