# SPDX-License-Identifier: AGPL-3.0-or-later
"""Selected exact229 checks; run only in the owning chat's ColabLinux runtime."""
from pathlib import Path
import itertools,json
if not Path('/content').is_dir():raise RuntimeError('Own ColabLinux required')
import coexact_partition_rank_diagnostic228 as base

def need(ok,message):
    if not ok:raise ValueError(message)

def partition_words(size):
    def extend(word):
        if len(word)==size:
            yield tuple(word);return
        for value in range(max(word)+2):yield from extend(word+[value])
    yield from extend([0])

def derivative_row(x,i,sites,index,n,central=False):
    row=[0]*len(sites)
    row[index[base.shift(x,i,n)]]+=1
    row[index[base.shift(x,i,n,-1) if central else x]]-=1
    return row

def drift_rows(D,n,central=False):
    sites=list(itertools.product(range(n),repeat=D));index={x:i for i,x in enumerate(sites)}
    return [[sum(derivative_row(x,j,sites,index,n,central)[k] for j in range(D)) for k in range(len(sites))] for x in sites]

def check_case(D,n,g,word,name,sharp=False):
    sites=list(itertools.product(range(n),repeat=D));V=len(sites);index={x:i for i,x in enumerate(sites)}
    need(len(word)==V and min(word)==0,'Partition word size/root')
    R=max(word)+1;need(set(word)==set(range(R)),'Nonempty consecutive block labels')
    labels=dict(zip(sites,word));anchors={a:next(x for x in sites if labels[x]==a) for a in range(R)}
    columns=[]
    for alpha in range(g):
        for i in range(D):
            for j in range(i+1,D):
                for x in sites:
                    u=base.plaquette(x,i,j,alpha,D,g,n)
                    need(base.valid_coexact_consequences(u,sites,D,g,n),'Actual delta-image consequences')
                    columns.append(base.column(u,labels,R,D,g))
    rows=[list(row) for row in zip(*columns)];rank=base.exact_rank(rows)
    constraints=[]
    for x in sites:
        anchor=anchors[labels[x]]
        for j in range(D):
            a=derivative_row(x,j,sites,index,n);b=derivative_row(anchor,j,sites,index,n)
            constraints.append([v-w for v,w in zip(a,b)])
    constraint_rank=base.exact_rank(constraints);potential_dim=V-1-constraint_rank
    need(potential_dim>=0,'Constants must remain in gradient-constraint kernel')
    expected=g*(D*R-D-potential_dim);lower=g*(D-1)*(R-1)
    need(rank==expected,'229 exact real annihilator dimension formula')
    need(rank>=lower,'229 sharp universal selected bound')
    need(potential_dim<=R-1,'Actual selected potential injection dimension')
    drift_rank=base.exact_rank(drift_rows(D,n))
    need(drift_rank==V-1,'Actual forward drift kernel has constants only')
    if sharp:need(rank==lower,'Selected coordinate-fibre sharpness')
    return {'D':D,'n':n,'g':g,'V':V,'partition':name,'R':R,'true_coexact_image_rank':rank,'gradient_constraint_rank':constraint_rank,'mean_zero_block_gradient_potential_dimension':potential_dim,'annihilator_formula_rank':expected,'sharp_lower_bound':lower,'forward_drift_rank':drift_rank,'fibre_equality_required':sharp}

def run():
    words=list(partition_words(4));need(len(words)==15 and len(set(words))==15,'All15four-site partitions')
    cases=[];completed=0
    for index,word in enumerate(words):
        cases.append(check_case(2,2,1,word,'all4sites-'+str(index)));completed+=1
    specs=[(2,1,1,'root'),(2,3,1,'stripes'),(3,3,1,'stripes'),(3,3,2,'stripes'),(3,2,1,'parity'),(4,2,1,'singletons')]
    for D,n,g,kind in specs:
        sites=list(itertools.product(range(n),repeat=D))
        if kind=='root':word=[0]*len(sites)
        elif kind=='stripes':word=[x[0] for x in sites]
        elif kind=='parity':word=[sum(x)%2 for x in sites]
        elif kind=='singletons':word=list(range(len(sites)))
        else:raise ValueError('Unknown fixed specification')
        cases.append(check_case(D,n,g,word,kind,kind=='stripes'));completed+=1
    need(completed==21 and len(cases)==21,'21completed cases before success')
    central=base.exact_rank(drift_rows(2,2,True));forward=base.exact_rank(drift_rows(2,2))
    projected=base.matrix_rank(3,3,1,'stripes',project_one=True)
    root=cases[0]
    wrong_harmonic_prediction=2*root['R']-root['mean_zero_block_gradient_potential_dimension']
    controls={'central_drift_Nyquist_kernel_rejected':central!=3 and forward==3,'omitted_constant_vector_harmonics_rejected':wrong_harmonic_prediction!=root['true_coexact_image_rank'],'projected_transverse_output_class_rejected':projected['true_image_rank']<2*(projected['R']-1)}
    required={'central_drift_Nyquist_kernel_rejected','omitted_constant_vector_harmonics_rejected','projected_transverse_output_class_rejected'}
    need(set(controls)==required,'Exact named real mutation controls')
    rejected=0
    for name in sorted(required):
        need(controls[name] is True,'Mutation was not actually rejected: '+name);rejected+=1
    need(rejected==3,'Three completed real rejections before success')
    return {'status':'SELECTED_SHARP_COEXACT_RANK229_CHECKED','completed_cases':completed,'all_partitions_of_D2n2':15,'cases':cases,'negative_controls':controls,'rejected_controls':rejected,'mutation_evidence':{'central_drift_D2n2_rank':central,'actual_forward_D2n2_rank':forward,'root_true_rank':root['true_coexact_image_rank'],'root_wrong_omitted_harmonic_prediction':wrong_harmonic_prediction,'projected_D3n3_stripes_rank':projected['true_image_rank'],'projected_false_bound':2*(projected['R']-1)},'scope':'21selected exact integer matrix cases, annihilator dimensions, forward drift and fibre equalities. One own runtime normal/-O is not independent clone replay. No fullL16coefficient-budgetfamily execution, all-size formal certificate, novelty priority, physical result or numerical paper grade.'}

if __name__=='__main__':print(json.dumps(run(),sort_keys=True))
