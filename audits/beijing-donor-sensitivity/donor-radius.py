"""Construct exact certificates on stored decimal loadings."""
import csv,json,itertools
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.optimize import linprog


def solve(label):
    with open(label+'-loadings.csv') as stream:
        rows=list(csv.reader(stream))[1:]
    stations=[r[0] for r in rows]
    if len(stations)!=len(set(stations)) or stations[0]!='G110003':
        raise ValueError('Unanticipated station indexing')
    matrix=sp.Matrix([[sp.Rational(v) for v in row[1:]] for row in rows])
    target=matrix[0,:].T
    floats=np.array(matrix,dtype=float)
    solved={}
    def node(removed):
        if removed in solved:return
        eligible=[i for i in range(1,len(rows)) if i not in removed]
        A=floats[eligible,:]
        model=linprog(-floats[0],A_ub=np.vstack((A,-A)),b_ub=np.ones(2*len(A)),bounds=(None,None),method='highs')
        if not model.success:raise ValueError(model.message)
        dual=np.array(model.ineqlin.marginals)
        active=np.abs(dual[:len(A)]-dual[len(A):])
        support=sorted(eligible[i] for i in np.argsort(-active)[:matrix.cols])
        block=matrix[support,:]
        weights=block.T.inv()*target
        direction=block.inv()*sp.Matrix([sp.sign(a) for a in weights])
        scale=max([sp.Integer(1)]+[abs((matrix[i,:]*direction)[0]) for i in eligible])
        direction=direction/scale
        upper=sum(map(abs,weights))
        lower=(target.T*direction)[0]
        if upper!=lower:raise ValueError(f'Uncertified basis at {removed}: {float(upper-lower)}')
        solved[removed]=dict(removed=list(removed),support=support,weights=list(map(str,weights)),direction=list(map(str,direction)),value=str(upper))
        if len(removed)<2:
            for i in support:node(tuple(sorted((*removed,i))))
    node(())
    best=max(solved,key=lambda k:sp.Rational(solved[k]['value']))
    return dict(target=stations[0],stations=stations,model=label,nodes=list(solved.values()),max_removed=[stations[i] for i in best],worst_diameter=str(2*sp.Rational(solved[best]['value'])),baseline_diameter=str(2*sp.Rational(solved[()]['value'])))


def diagnostics():
    def load(name):
        with open(name+'.csv') as f:
            rows=list(csv.reader(f))[1:]
        return {r[0]:r[1:] for r in rows}
    raw=load('raw');full=load('full-pre');restricted=load('restricted-pre')
    changes=[]; dependencies=[]
    orders=Path('fit-info.txt').read_text().splitlines()[1].split(' ',1)[1].split(',')
    if orders!=list(map(str,range(1,73))):raise ValueError('Inspect extended time order before attributing dependence')
    for station,row in raw.items():
        for j in range(48):
            if row[j]:continue
            right=next((i for i in range(j+1,len(row)) if row[i]),None)
            if right is not None and right>=48:dependencies.append([station,j+1,right+1])
            if full[station][j]!=restricted[station][j]:
                changes.append([station,j+1,full[station][j],restricted[station][j]])
    return dict(changed=changes,cross_boundary=dependencies,n=len(raw))
if __name__=='__main__':
    d=diagnostics()
    Path('diagnostics.json').write_text(json.dumps(d,indent=2))
    for scenario in ('full','restricted'):
        out=solve(scenario)
        Path(scenario+'-radii.json').write_text(json.dumps(out))
        print(scenario,d['n'],len(d['changed']),len(out['nodes']),float(sp.Rational(out['worst_diameter'])),flush=True)

