"""Actual trivial-background cochain stencil replay. Execute in own Colab Linux."""
from fractions import Fraction as F
import contextlib
import io
import json
with contextlib.redirect_stdout(io.StringIO()):
    import exact165 as scalar


def check(ok, label):
    if not ok:
        raise ValueError(label)


xs = scalar.points
dim = 72  # D3,n2,Nc2, internal dimension Nc^2-1=3
coords = [(x,j,a) for x in xs for j in range(3) for a in range(3)]


def row(terms):
    r = {}
    for key, value in terms:
        index = coords.index(key)
        r[index] = r.get(index,F(0))+value
    return {i:v for i,v in r.items() if v}


def shift(x,i):
    y=list(x)
    y[i] ^= 1
    return tuple(y)


def gram(rows, weights=None):
    m = [[F(0) for _ in range(dim)] for _ in range(dim)]
    if weights is None:
        weights = [1]*len(rows)
    for r,w in zip(rows,weights):
        for i,vi in r.items():
            for j,vj in r.items():
                m[i][j] += w*vi*vj
    return m


curl, plaq, div, gradient, weights = [],[],[],[],[]
for x in xs:
    for a in range(3):
        div.append(row([((x,j,a),1) for j in range(3)] +
                       [((shift(x,j),j,a),-1) for j in range(3)]))
        for i in range(3):
            for j in range(i+1,3):
                plaq.append((x,i,j,a))
                curl.append(row([((shift(x,i),j,a),1),((x,j,a),-1),
                                 ((shift(x,j),i,a),-1),((x,i,a),1)]))
    ax = F(6+(-1)**x[0]+4*(-1)**x[1])
    for i in range(3):
        for j in range(3):
            for a in range(3):
                gradient.append(row([((shift(x,i),j,a),1),((x,j,a),-1)]))
                weights.append(ax-1)


gc, gd, gr = gram(curl),gram(div),gram(gradient,weights)
expected_scalar = scalar.actual()
expected = [[expected_scalar[xs.index(x)][xs.index(y)] if (j,a)==(k,b) else F(0)
             for y,k,b in coords] for x,j,a in coords]


def matrix_identity(curl_factor=1, divergence_factor=1):
    combined = [[curl_factor*gc[i][j]+divergence_factor*gd[i][j]+gr[i][j]
                 for j in range(dim)] for i in range(dim)]
    check(combined==expected,'actual full Hodge plus repair matrix')
    return combined


def field(mask, direction=2):
    return [scalar.chi(mask,x) if j==direction and a==0 else F(0)
            for x,j,a in coords]


def transpose_apply(rows, b):
    result=[F(0)]*dim
    for r,weight in zip(rows,b):
        for i,value in r.items():
            result[i] += value*weight
    return result


def divergence_zero(v):
    check(all(sum((value*v[i] for i,value in r.items()),F(0))==0 for r in div),
          'actual backward divergence')


u=field(2)
v=[-2*x+y for x,y in zip(field(1),field(3))]
bu=[-scalar.chi(2,x)/2 if (i,j,a)==(1,2,0) else F(0) for x,i,j,a in plaq]
bv=[scalar.chi(1,x)-scalar.chi(3,x)/2 if (i,j,a)==(0,2,0) else F(0)
    for x,i,j,a in plaq]


def potentials(sign=1):
    check(transpose_apply(curl,[sign*b for b in bu])==u,'actual U coexact potential')
    check(transpose_apply(curl,bv)==v,'actual V coexact potential')


def project(w):
    return [(w[i]+w[coords.index((shift(x,0),j,a))])/2
            for i,(x,j,a) in enumerate(coords)]


physical = matrix_identity()
potentials()
divergence_zero(u)
divergence_zero(v)
check(project(v)==[F(0)]*dim and project(u)==u,'actual rectangle means projection')
check(scalar.dot(u,u)==8 and scalar.dot(v,v)==40,'unnormalized witness norms')
check(scalar.dot(u,scalar.mv(physical,u))==192 and
      scalar.dot(v,scalar.mv(physical,v))==640,'actual witness energies')
check(scalar.dot(u,scalar.mv(physical,v))==32,'actual cross energy')
# Whole kernel inequality transfers by the FULL matrix direct-sum identity
# above and the scalar complete compression check, not just two test vectors.
scalar.verify(expected_scalar)
for k in (F(0),F(1),F(100),F(10**6)):
    t=-(8+k)/8-1
    w=[x+t*y for x,y in zip(u,v)]
    divergence_zero(w)
    q=scalar.dot(w,scalar.mv(physical,w))-16*scalar.dot(w,w)
    check(q+k*scalar.dot(project(w),project(w))==-64,'actual coexact countervector')

mutations=[]
for name, action in (
    ('omit_divergence',lambda: matrix_identity(divergence_factor=0)),
    ('duplicate_unordered_curl',lambda: matrix_identity(curl_factor=2)),
    ('wrong_potential_sign',lambda: potentials(sign=-1)),
    ('move_witness_to_first_component',lambda: divergence_zero(field(1,direction=0)))):
    try:
        action()
    except ValueError as error:
        mutations.append({'mutation':name,'rejection':str(error)})
    else:
        raise ValueError('Mutation accepted: '+name)
check(len(mutations)==4,'explicit mutation count')
print(json.dumps({'status':'EXACT_COEXACT_RECTANGLE_PASS','mutation_count':4,
                  'mutations':mutations,'physical_dimension':dim,'D':3,'n':2,'Nc':2,
                  'internal_dimension':3,'curl_rows':len(curl),'divergence_rows':len(div),
                  'gradient_rows':len(gradient),'rectangles':4,'output_dimension':36,
                  'full_form_matrix_identity':True,'actual_coexact_potentials':True,
                  'kernel_coercivity':16,'critical_repair_impossible':True,
                  'independent_review':False,'Lean_verified':False,
                  'asymptotic_rank_conjecture_refuted':False},sort_keys=True))
