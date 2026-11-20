"""Find a single probability space for all four threshold-specific tables."""
from fractions import Fraction as F
from pathlib import Path
import json
from hss_support import solve
def run():
    data=json.loads(Path('hss-edges.json').read_text())
    vals=[1+F(s)/100 for s in data['rows']['0.5']]
    u,v,w,p,q,r=vals
    weights=[F(1,4),F(1,2),F(1,4)]
    for amp in [F(k,100) for k in [2,4,8,16,32,64]]:
        x=[u-amp,u,u+amp];ix=[h/vv for h,vv in zip(weights,x)]
        for shift in [F(i,100) for i in range(-30,31)]:
            y=solve([weights,ix,[0,1,0]],[v,p,v+shift])
            if y is None or min(y)<=0:continue
            z=solve([weights,ix,[h/vv for h,vv in zip(weights,y)]],[w,q,r])
            if z is None or min(z)<=0:continue
            mat=[[F(1)]*3,x,y,z]
            for (i,j),t in zip([(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)],vals):
                if sum(h*a/b for h,a,b in zip(weights,mat[i],mat[j]))!=t:raise ValueError('Not exact')
            return dict(weights=weights,mat=mat,amp=amp,shift=shift)
    raise ValueError('No common-weight construction')
if __name__=='__main__':print(json.dumps(run(),default=str,sort_keys=True,indent=2))

