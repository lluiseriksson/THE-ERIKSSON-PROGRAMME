"""Replay exact bounds and test them against convex corners of the observation boxes."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
from jeju_regret import run, require
def read(name):
    return json.loads(Path(name).read_text())
def interpolate(vertices,x):
    for (a,u),(b,v) in zip(vertices,vertices[1:]):
        if a<=x<=b:return ((b-x)*u+(x-a)*v)/(b-a)
    raise ValueError(x)
def main():
    data=read('planning-tables.json');point=read('extra-point.json');observed=read('certificate.json')
    centres={int(r[0]):F(r[1].split()[0]) for r in data['tables']['10']}
    tally=0
    for key,extra in [('table_only',None),('with_extra_point',point)]:
        d=run(data,extra)
        require(json.loads(json.dumps(d,default=str))==observed[key],'Certificate differs')
        for r in data['tables']['11']:
            y=int(r[0]);c=centres[y]
            heights={c+k:F(cell.split('/')[0]) for k,cell in zip([-10,-5,0,5,10],r[1:])}
            if extra and y==2038:heights[F(60)]=F(point['energy_GWh'])
            xs=sorted(heights);mesh=[*map(F,d['grid']),d['continuous']['share']]
            best={m:None for m in mesh}
            for signs in product([-1,1],repeat=len(xs)):
                ys=[heights[x]+F(s,20) for x,s in zip(xs,signs)]
                slopes=[(v-u)/(b-a) for a,b,u,v in zip(xs,xs[1:],ys,ys[1:])]
                if slopes!=sorted(slopes) or min(ys)!=ys[xs.index(c)]:continue
                for m in mesh:
                    risk=interpolate(list(zip(xs,ys)),m)-ys[xs.index(c)]
                    if best[m] is None or risk>best[m]:best[m]=risk
            for m in mesh:require(best[m]==interpolate(d['vertices'][y],m),'Corner enumeration mismatch')
            tally+=len(mesh)
    print(json.dumps(dict(corner_checks=tally,augmented=observed['with_extra_point']['continuous'],table_only=observed['table_only']['continuous'],grid=observed['with_extra_point']['grid']),sort_keys=True))
if __name__=='__main__':main()
