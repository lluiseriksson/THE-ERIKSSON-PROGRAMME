# SPDX-License-Identifier: AGPL-3.0-or-later
"""Selected exact tests of228coexact rank lemma; execute only in owned ColabLinux."""
from pathlib import Path
import itertools,json,math
if not Path('/content').is_dir():raise RuntimeError('Own ColabLinux required')

def need(value,message):
    if not value:raise ValueError(message)

def shift(x,i,n,sign=1):
    y=list(x);y[i]=(y[i]+sign)%n;return tuple(y)

def add(u,x,k,v):
    key=(x,k);u[key]=u.get(key,0)+v
    if not u[key]:del u[key]

def plaquette(x,i,j,alpha,D,g,n,mutation=None):
    # Actual B_ij=delta_x e_alpha,B_ji=-delta_x e_alpha, with backward delta.
    u={};add(u,x,i*g+alpha,1)
    add(u,shift(x,j,n,-1 if mutation=='one_wrong_shift' else 1),i*g+alpha,-1)
    sign=1 if mutation=='wrong_codifferential_sign' else -1
    add(u,x,j*g+alpha,sign);add(u,shift(x,i,n),j*g+alpha,-sign)
    return u

def valid_coexact_consequences(u,sites,D,g,n):
    # Necessary consequences checked on actual field values, not fabricated labels.
    for alpha in range(g):
        for x in sites:
            div=sum(u.get((x,i*g+alpha),0)-u.get((shift(x,i,n,-1),i*g+alpha),0) for i in range(D))
            if div:return False
    return all(sum(u.get((x,k),0) for x in sites)==0 for k in range(D*g))

def exact_rank(rows):
    if not rows:return 0
    a=[row[:] for row in rows];r=0
    for col in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][col]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r];p=a[r][col]
        for i in range(r+1,len(a)):
            q=a[i][col]
            if not q:continue
            a[i]=[p*v-q*w for v,w in zip(a[i],a[r])]
            divisor=math.gcd(*a[i])
            if divisor>1:a[i]=[v//divisor for v in a[i]]
        r+=1
        if r==len(a):break
    return r

def column(u,labels,R,D,g,project_one=False):
    out=[0]*(R*(1 if project_one else D*g))
    for (x,k),v in u.items():
        if project_one:
            if k==0:out[labels[x]]+=v
        else:out[labels[x]*D*g+k]+=v
    return out

def matrix_rank(D,n,g,kind,project_one=False):
    sites=list(itertools.product(range(n),repeat=D))
    if kind=='root':raw={x:0 for x in sites}
    elif kind=='singletons':raw={x:i for i,x in enumerate(sites)}
    elif kind=='stripes':raw={x:x[0] for x in sites}
    elif kind=='parity':raw={x:sum(x)%2 for x in sites}
    elif kind=='diagonal3':raw={x:sum(x)%3 for x in sites}
    elif kind=='disconnected4':raw={x:sum((i+1)*v for i,v in enumerate(x))%4 for x in sites}
    else:raise ValueError('Unknown partition')
    relabel={v:i for i,v in enumerate(sorted(set(raw.values())))}
    labels={x:relabel[v] for x,v in raw.items()};R=len(relabel)
    columns=[]
    for alpha in range(g):
        for i in range(D):
            for j in range(i+1,D):
                for x in sites:
                    u=plaquette(x,i,j,alpha,D,g,n)
                    need(valid_coexact_consequences(u,sites,D,g,n),'Actual coexact field consequences')
                    columns.append(column(u,labels,R,D,g,project_one))
    rows=[list(row) for row in zip(*columns)]
    rank=exact_rank(rows)
    # q_B differs from these block sums by nonzero known row factors; rank is identical.
    return {'D':D,'n':n,'g':g,'partition':kind,'R':R,'columns_actual_delta_basis':len(columns),'output_rows':len(rows),'true_image_rank':rank,'lower_numerator':g*(R-1),'lower_denominator':D}

def run():
    need(exact_rank([[0,0],[0,0]])==0,'Rank zero control')
    need(exact_rank([[2,4],[1,2]])==1,'Rank dependent control')
    need(exact_rank([[0,1,2],[1,0,3],[0,0,1]])==3,'Rank pivot control')
    specifications=[(3,1,1,'root'),(3,1,2,'root'),(3,2,1,'root'),(3,2,1,'singletons'),(3,2,2,'parity'),(3,3,1,'stripes'),(3,3,2,'diagonal3'),(3,3,1,'disconnected4'),(3,3,1,'singletons'),(4,2,2,'singletons')]
    cases=[]
    for D,n,g,kind in specifications:
        case=matrix_rank(D,n,g,kind)
        need(D*case['true_image_rank']>=case['lower_numerator'],'228lemma selected exact rank')
        cases.append(case)
    sites=list(itertools.product(range(3),repeat=3));x=(0,0,0)
    sign=plaquette(x,0,1,0,3,1,3,'wrong_codifferential_sign')
    wrong_shift=plaquette(x,0,1,0,3,1,3,'one_wrong_shift')
    projected=matrix_rank(3,3,1,'stripes',project_one=True)
    controls={'wrong_codifferential_sign_rejected':not valid_coexact_consequences(sign,sites,3,1,3),'one_wrong_shift_rejected':not valid_coexact_consequences(wrong_shift,sites,3,1,3),'dropping_transverse_outputs_breaks_bound':3*projected['true_image_rank']<projected['lower_numerator']}
    need(all(controls.values()),'Actual field/output mutations must be detected')
    return {'status':'SELECTED_EXACT_COEXACT_RANK_LEMMA_DIAGNOSTICS_CHECKED','cases':cases,'negative_controls':controls,'negative_controls_rejected':len(controls),'scope':'Ten selected actual coexact delta-image rank matrices; nonzero normalized row-scaling invariance; three real field/output mutations. Does not execute the fixedL16multi-bump coefficient/budget family, prove all sizes, certify historical novelty, provide numerical paper grade or independent clone replay.','projected_measurement_counterexample':projected}

if __name__=='__main__':print(json.dumps(run(),sort_keys=True))
