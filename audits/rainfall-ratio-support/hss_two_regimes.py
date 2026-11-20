"""Construct exact feasible witnesses for the equal-weight two-regime interpretation."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from math import sqrt
import json,sympy as S
def roots(coeffs):
    a,b,c=coeffs
    if a==0:return [] if b==0 else [-c/b]
    disc=b*b-4*a*c
    if disc<0:return []
    return [(-b+sign*S.sqrt(S.Rational(disc)))/(2*a) for sign in [-1,1]]
def witness(values):
    u,v,w,p,q,r=values
    A=u*v-p*u*u;B=u*w-q*u*u
    co=[r*p*p-p*q,v*w-r*v*v+2*r*p*A-p*B-q*A,r*A*A-A*B]
    # Fast screen only. Every claimed witness is subsequently checked using algebraic numbers.
    a,b,c=map(float,co)
    if a and b*b-4*a*c>=0:
        cand=[(-b+sgn*sqrt(b*b-4*a*c))/(2*a) for sgn in [-1,1]]
    elif not a and b:cand=[-c/b]
    else:return None
    if not any(0<z<float(u*u) and (float(p)*z+float(A))**2<float(v*v)*z and (float(q)*z+float(B))**2<float(w*w)*z for z in cand):return None
    for z in roots(co):
        if not (0<z<u*u and (p*z+A)**2<v*v*z and (q*z+B)**2<w*w*z):continue
        require=S.simplify
        if require(co[0]*z*z+co[1]*z+co[2])!=0:raise ValueError('Bad root')
        d=S.sqrt(z)
        ds=[d,(p*z+A)/d,(q*z+B)/d]
        for (i,j),ratio in zip([(0,1),(0,2),(1,2)],[p,q,r]):
            ui,uj=values[i],values[j];di,dj=ds[i],ds[j]
            if require(ui*uj-di*dj-ratio*(ui*ui-di*di))!=0:raise ValueError('Ratio not reproduced')
        return dict(z=str(z),coefficients=list(map(str,co)),means=list(map(str,values[:3])),ratios=list(map(str,values[3:])),deviations_approx=[float(x) for x in ds])
def main():
    data=json.loads(Path('hss-edges.json').read_text());out={}
    for name,row in data['rows'].items():
        result=None;tested=0
        for offsets in product([0,-1,1],repeat=6):
            # Interior offsets guarantee that the printed decimals round back without tie rules.
            values=[1+(F(s)+F(k,4*10**len(s.split('.')[1])))/100 for s,k in zip(row,offsets)]
            tested+=1;result=witness(values)
            if result:
                result['offsets_quarter_last_digit']=offsets;break
        out[name]=dict(box_witness=result,candidates_tested=tested)
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()

