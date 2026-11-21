"""Exact deletion classifications and integer bounds constrained by published margins."""
import hashlib, itertools, json, math, zipfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csc_matrix

METHODS = ['M0','M1','M2','M2a','M2b','M3','LIVE']
Y = [32,36,61,77,69,85,87]
X = [0,0,2,6,3,11,12]
YU = [25,28,35,47,39,51,51]
XU = [0,0,1,5,2,8,9]
# Numbers of top-ten hits reconstructed within each in-catalog phenomenon, Table 5.
GROUP = {
    'standard':[14,15,19,21,19,21,22], 'typo':[0,1,2,3,6,7,7],
    'truncated':[4,4,4,5,4,5,6], 'dialect_phrase':[0,0,0,4,0,4,4],
    'dialect_word':[1,1,2,4,2,4,4], 'spelling_variant':[1,2,2,4,2,4,2],
    'loanword':[2,2,3,3,3,3,3], 'brand':[2]*7, 'ambiguous':[1]*7}
def support(x,y):
    low,high=Fraction(0),None
    for j in range(7):
        if j==5:continue
        dx=x[5]-x[j];dy=y[5]-y[j]
        if dx==0:
            if dy<=0:return False
        elif dx>0:
            bound=Fraction(dy,dx)
            high=bound if high is None else min(high,bound)
        else:low=max(low,Fraction(dy,dx))
    return high is None or low<high

def blocks(zpath):
    assert hashlib.sha256(zpath.read_bytes()).hexdigest()=='de12df29cbab125814ddd31141f7e4a5051dae5159d6da08ee75d4a5fa74cc86'
    with zipfile.ZipFile(zpath) as archive:
        members={i.filename.replace(chr(92),'/'):i for i in archive.infolist()}
        freq={r['q']:r['n'] for r in json.loads(archive.read(members['data/queries.json']))}
        groups=Counter()
        for line in archive.read(members['data/labels.tsv']).decode('utf-8-sig').splitlines():
            if not line or line.startswith('#'):continue
            query,cls,group,incat,*_=line.split('\t')
            if cls in ('product','brand'):
                groups[group if incat in ('yes','partial') else 'gap',freq[query]]+=1
    return groups

def run(zpath):
    groups=blocks(zpath)
    vars=[]; scores=[]; features=[]
    for (g,n),count in sorted(groups.items()):
        size=sum(v for (label,_),v in groups.items() if label==g)
        for p in itertools.product((0,1),repeat=7):
            if g=='gap':
                if p[0] or p[1] or p[2]>p[5]:continue
            else:
                if not (p[0]<=p[1]<=p[2] and all(p[2]<=p[i] for i in [3,4,5])):continue
                if any(p[j] and GROUP[g][j]==0 or not p[j] and GROUP[g][j]==size for j in range(7)):continue
            x=[v-(n*h if g=='gap' else 0) for v,h in zip(X,p)]
            y=[v-(n*h if g!='gap' else 0) for v,h in zip(Y,p)]
            win=support(x,y)
            if g!='gap' and p[6] and not p[5]:
                assert all(3*y[5]-4*x[5]>3*y[j]-4*x[j] for j in range(7) if j!=5)
            vars.append((g,n,''.join(map(str,p))))
            scores.append(int(win))
            row={('block',g,n):1}
            for j,hit in enumerate(p):
                row['events',g=='gap',j]=n*hit
                row['group',g,j]=hit
            if g!='gap':row['gain',]=int(p[6]>p[5])
            features.append(row)
    rhs={('block',g,n):v for (g,n),v in groups.items()}
    rhs.update({('events',gap,j):v for gap,vals in [(True,X),(False,Y)] for j,v in enumerate(vals)})
    rhs.update({('group',g,j):v for g,vals in dict(GROUP,gap=XU).items() for j,v in enumerate(vals)})
    rhs['gain',]=2
    assert list(map(sum,zip(*GROUP.values())))==YU
    assert not support(X,Y)
    A=np.array([[row.get(key,0) for row in features] for key in rhs],dtype=int)
    rhs_array=np.array(list(rhs.values()));bounds=Bounds(0,[groups[g,n] for g,n,_ in vars])
    saved={}
    for direction,name in [(1,'minimum'),(-1,'maximum')]:
        result=milp(np.array(scores)*direction,integrality=np.ones(len(vars)),bounds=bounds,
                    constraints=LinearConstraint(csc_matrix(A),rhs_array,rhs_array),
                    options={'mip_rel_gap':0.0,'time_limit':150})
        if not result.success:raise ValueError(result.message)
        v=np.rint(result.x).astype(int)
        assert np.all(A@v==rhs_array) and np.all(v>=0) and np.all(v<=bounds.ub)
        total=int(v@np.array(scores))
        assert abs(result.mip_dual_bound-direction*total)<1e-5
        saved[name]=dict(count=total,solver_bound=float(result.mip_dual_bound),
                         witness=[[*item,int(k)] for item,k in zip(vars,v) if k])
    return dict(definition='Single deletion removes all events of one query. A win is a strict maximum over all seven methods for some positive false-hit cost.', methods=METHODS,
                constraints='Frequency blocks from the supplement, Table 3 success and false-hit totals, Table 4 paired success and gap claims, Table 5 success counts. The report does not constrain precision or ranking.',
                blocks=[[g,n,k] for (g,n),k in sorted(groups.items())],extrema=saved)
if __name__=='__main__':print(json.dumps(run(Path('source.zip')),sort_keys=True))
