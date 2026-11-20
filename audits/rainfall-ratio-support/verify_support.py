"""Verify finite-support certificates without the witness search."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json
import sympy as S
def read(n):return json.loads(Path(n).read_text())
def need(x,msg):
    if not x:raise ValueError(msg)
def verify_two(values,record):
    u,v,w=map(S.Rational,record['means']);p,q,r=map(S.Rational,record['ratios'])
    for m,s in zip([u,v,w,p,q,r],values):
        width=S.Rational(1,200*10**len(s.split('.')[1]))
        need(abs(m-1-S.Rational(s)/100)<width,'Outside rounding bin')
    Z=S.symbols('Z');a=u*v-p*u*u;b=u*w-q*u*u
    # Independent elimination: impose the (3,2) average after clearing its denominator.
    num=S.expand((v*w-r*v*v)*Z-(p*Z+a)*(q*Z+b)+r*(p*Z+a)**2)
    for z in S.solve(num,Z):
        if z.is_real is not True or not 0<z<u*u:continue
        d=S.sqrt(z);deviations=[d,(p*z+a)/d,(q*z+b)/d]
        if not all(abs(h)<m for h,m in zip(deviations,[u,v,w])):continue
        levels=[[1,1]]+[[m-h,m+h] for m,h in zip([u,v,w],deviations)]
        for (i,j),m in zip([(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)],[u,v,w,p,q,r]):
            lhs=sum(levels[i][k]/levels[j][k] for k in range(2))/2
            need(S.simplify(lhs-m)==0,'Wrong two-regime mean')
        return
    raise ValueError('Missing positive solution')
def main():
    data=read('hss-edges.json');sup=read('support.json');cy=read('cycles.json');wit=read('witnesses.json');mins={}
    for k,vs in data['rows'].items():
        centres=[1+F(s)/100 for s in vs]
        half=[F(1,200*10**len(s.split('.')[1])) for s in vs]
        bounds=[(m-h,m+h) for m,h in zip(centres,half)]
        maxstep={}
        for (i,j),(l,h) in zip(data['columns'],bounds):
            maxstep[j,i]=h;maxstep[i,j]=1/l
        cyc,claimed=cy[k]['failing_at_printed_precision'][0];prod=F(1)
        for i in range(len(cyc)):prod*=maxstep[cyc[i-1],cyc[i]]
        need(prod==F(claimed) and prod<1,'No exclusion of one regime')
        if k=='0.5':
            # Fix bounds of normalized ratios directly by interval monotonicity.
            (ul,uh),(vl,vh),(wl,wh),(pl,ph),(ql,qh),(rl,rh)=bounds
            upper_a=ph*uh/vl-1;lower_b=ql*ul/wh-1;upper_c=rh*vh/wl-1
            need(upper_a<0 and lower_b-upper_a>max(0,upper_c),'No affine-factor exclusion')
            mat=[list(map(F,row)) for row in sup[k]['three_regime_scores']]
            need(min(min(row) for row in mat)>0,'Non-positive scores')
            for (i,j),m in zip([(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)],centres):
                need(sum(a/b for a,b in zip(mat[i],mat[j]))==3*m,'Wrong three-regime mean')
            mins[k]=3
        else:
            verify_two(vs,wit[k]['box_witness']);mins[k]=2
        for key,ix in {'210':(0,3,1),'310':(0,4,2),'320':(1,5,2),'321':(3,5,4)}.items():
            i,j,h=ix
            tests=[x-y*z for x,y,z in product(bounds[h],bounds[i],bounds[j])]
            need(list(map(F,sup[k]['covariance'][key]))==[min(tests),max(tests),max(0,min(tests),-max(tests))],'Bad covariance bound')
    common=read('common.json')
    weights=list(map(F,common['weights']));mat=[list(map(F,row)) for row in common['mat']]
    need(weights==[F(1,4),F(1,2),F(1,4)] and min(min(r) for r in mat)>0,'Common witness positivity')
    vals=[1+F(v)/100 for v in data['rows']['0.5']]
    for (i,j),v in zip([(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)],vals):
        need(sum(h*a/b for h,a,b in zip(weights,mat[i],mat[j]))==v,'Wrong common-space mean')
    print(json.dumps(dict(minimum_support=mins,covariance_boxes=16,ratios_per_witness=6),sort_keys=True))
if __name__=='__main__':main()

