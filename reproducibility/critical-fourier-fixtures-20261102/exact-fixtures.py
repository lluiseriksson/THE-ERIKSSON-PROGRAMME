"""Exact finite diagnostics for the critical Fourier/flow adapters.
Run only in own Colab Linux. No Python assert controls acceptance.
This does NOT prove the general theorem or provide independent review.
"""
from fractions import Fraction as Q
import copy, json

N, D = 16, 4

def need(ok, message):
    if not ok:
        raise ValueError(message)

def zero(n=N, m=N):
    return [[Q(0) for _ in range(m)] for _ in range(n)]

def eye(n=N):
    a = zero(n, n)
    for i in range(n): a[i][i] = Q(1)
    return a

def tr(a): return sum((a[i][i] for i in range(len(a))), Q(0))
def tp(a): return [list(x) for x in zip(*a)]
def scale(a, s): return [[v*s for v in row] for row in a]
def add(a, b): return [[x+y for x, y in zip(r, s)] for r, s in zip(a, b)]
def sub(a, b): return add(a, scale(b, -1))
def mul(a, b):
    bt = tp(b)
    return [[sum((x*y for x,y in zip(r,s)), Q(0)) for s in bt] for r in a]
def diag(v):
    a = zero(len(v), len(v))
    for i,x in enumerate(v): a[i][i] = Q(x)
    return a

def inverse(a):
    n = len(a); w = [r[:] + s[:] for r,s in zip(a, eye(n))]
    for k in range(n):
        pivot = next((i for i in range(k,n) if w[i][k]), None)
        need(pivot is not None, 'inverse singular')
        w[k], w[pivot] = w[pivot], w[k]
        t = w[k][k]; w[k] = [x/t for x in w[k]]
        for i in range(n):
            if i != k and w[i][k]:
                t = w[i][k]; w[i] = [x-t*y for x,y in zip(w[i],w[k])]
    return [r[n:] for r in w]

def inertia(a):
    """Exact symmetric congruence: scalar pivots or zero-diagonal 2x2 blocks."""
    need(a == tp(a), 'inertia asymmetric input')
    w = copy.deepcopy(a); pos = neg = nul = 0
    while w:
        n = len(w)
        pivot = next((i for i in range(n) if w[i][i]), None)
        if pivot is not None:
            order = [pivot] + [i for i in range(n) if i != pivot]
            w = [[w[i][j] for j in order] for i in order]
            s = w[0][0]
            pos += int(s > 0); neg += int(s < 0)
            w = [[w[i][j]-w[i][0]*w[0][j]/s for j in range(1,n)] for i in range(1,n)]
        else:
            pair = next(((i,j) for i in range(n) for j in range(i+1,n) if w[i][j]), None)
            if pair is None:
                nul += n; break
            i,j = pair; order = [i,j]+[k for k in range(n) if k not in pair]
            w = [[w[i][j] for j in order] for i in order]; b = w[0][1]
            pos += 1; neg += 1
            w = [[w[i][j]-(w[i][0]*w[1][j]+w[i][1]*w[0][j])/b
                  for j in range(2,n)] for i in range(2,n)]
    return pos, neg, nul

def psd(a): return inertia(a)[1] == 0
def count_above(a, s): return inertia(sub(scale(eye(len(a)), s), a))[1]

ID = eye(); CONST = scale([[Q(1)]*N for _ in range(N)], Q(1,N))
MEAN0 = sub(ID, CONST)
FOURIER = [[Q((-1)**((x & k).bit_count()),4) for k in range(N)] for x in range(N)]
DERIV = []
for i in range(D):
    d = zero()
    for x in range(N): d[x][x ^ (1 << i)] += 1; d[x][x] -= 1
    DERIV.append(d)
L0 = zero()
for d in DERIV: L0 = add(L0, mul(tp(d),d))
LAM = [Q(4*k.bit_count()) for k in range(N)]
L0PLUS = mul(mul(FOURIER,diag([1/x if x else Q(0) for x in LAM])),FOURIER)

def lap(a):
    out = zero()
    for d in DERIV: out = add(out,mul(mul(tp(d),diag(a)),d))
    return out

def make(a):
    a = list(map(Q,a)); la = lap(a)
    inv = sub(inverse(add(la, CONST)),CONST)
    bi = [mul(mul(mul(mul(L0PLUS,tp(d)),diag([1/x for x in a])),d),L0PLUS) for d in DERIV]
    b = zero()
    for v in bi: b = add(b,v)
    raw = [Q((7*i)%11) for i in range(N)]; mean = sum(raw)/N
    f = [[x-mean] for x in raw]
    flows = [mul(mul(d,L0PLUS),f) for d in DERIV]
    return dict(a=a,mean=sum(a)/N,la=la,inv=inv,bi=bi,b=b,f=f,flows=flows)

def verify(v):
    a,la,inv,bi,b,f,flows = (v[k] for k in ['a','la','inv','bi','b','f','flows'])
    need(len(a)==N and min(a)>=1 and max(a)<=2*v['mean'], 'actual profile class')
    need(sum(a)/N==v['mean'], 'actual arithmetic mean')
    need(la==lap(a), 'actual forward-start weighted Laplacian')
    need(mul(FOURIER,FOURIER)==ID, 'normalized unitary Fourier')
    need(mul(L0,L0PLUS)==MEAN0, 'unweighted actual pseudoinverse')
    need(mul(la,inv)==MEAN0 and inv==tp(inv), 'weighted actual pseudoinverse')
    need(mul(la,CONST)==zero(), 'constant kernel')
    need(inertia(la)==(15,0,1), 'actual positive mean-zero operator')
    need(bi==[mul(mul(mul(mul(L0PLUS,tp(d)),diag([1/x for x in a])),d),L0PLUS) for d in DERIV],
         'actual comparison component matrices')
    expected = zero()
    for w in bi: expected=add(expected,w)
    need(b==expected, 'actual comparison sum')
    need(psd(sub(b,inv)), 'inverse comparison wrong direction or coefficient')
    div=zero(N,1); optimal=[]; cross=Q(0); excess=Q(0); energy=Q(0)
    for d,j in zip(DERIV,flows):
        need(j==mul(mul(d,L0PLUS),f), 'actual feasible flow entries')
        div=add(div,mul(tp(d),j))
        js=mul(mul(mul(diag(a),d),inv),f); optimal.append(js)
        k=sub(j,js)
        cross+=mul(mul(tp(js),diag([1/x for x in a])),k)[0][0]
        excess+=mul(mul(tp(k),diag([1/x for x in a])),k)[0][0]
        energy+=mul(mul(tp(j),diag([1/x for x in a])),j)[0][0]
    need(div==f and cross==0, 'flow divergence or orthogonal cross term')
    need(energy==mul(mul(tp(f),inv),f)[0][0]+excess, 'flow energy identity')
    ls=[]; densities=[]
    for i,d in enumerate(DERIV):
        z=[Q(-2) if k & (1<<i) else Q(0) for k in range(N)]
        need(mul(d,FOURIER)==mul(FOURIER,diag(z)), 'actual directed Fourier symbol')
        g=[z[k]/LAM[k] if LAM[k] else Q(0) for k in range(N)]
        g2=[x*x for x in g]
        weak=max(t*t*sum(x>=t for x in g2)/N for t in set(g2) if t)
        need(weak<=Q(3,4)**D, 'normalized weak Fourier bound')
        ls.append(weak)
        aa=mul(mul(FOURIER,diag(g2)),FOURIER)
        ap=mul(mul(FOURIER,diag([1/x if x else Q(0) for x in g2])),FOURIER)
        test_vectors=[[[Q(int(x==0))] for x in range(N)],[[Q((x*5)%7-3)] for x in range(N)]]
        gammas=[scale(aa,Q(1,2))]
        for u in test_vectors:
            au=mul(aa,u); r=mul(tp(u),au)[0][0]
            need(r>0, 'density fixture vector annihilated')
            gammas.append(scale(mul(au,tp(au)),1/r))
        for gamma in gammas:
            need(psd(gamma) and psd(sub(aa,gamma)), 'density constraint0<=gamma<=A')
            lhs=tr(mul(ap,gamma)); rhs=sum(gamma[x][x]**2 for x in range(N))/(12*weak)
            need(lhs>=rhs, 'finite p2 density inequality')
            densities.append(dict(trace=str(lhs),lower=str(rhs)))
    counts=[]
    for c in [Q(1,2),Q(4),Q(10),Q(40)]:
        low=inertia(sub(scale(ID,c),la))[0]
        inverse_count=count_above(inv,1/c)
        need(low==1+inverse_count, 'constant mode or inversion multiplicity')
        sum_count=count_above(b,1/c)
        parts=[count_above(x,1/(c*D)) for x in bi]
        need(inverse_count<=sum_count<=sum(parts), 'inverse/minmax noncommuting counts')
        for k,w in enumerate(bi):
            bound=12*ls[k]*(c*D)**2*sum(1/x**2 for x in a)
            need(parts[k]<=bound, 'finite Cwikel component count')
        bound=1+12*Q(3,4)**D*D**3*c*c*sum(1/x**2 for x in a)
        need(low<=bound, 'actual low-count endpoint bound')
        if len(set(a))==1:
            need(low==sum(x*a[0]<c for x in LAM), 'uniform exact Fourier multiplicities')
        counts.append(dict(c=str(c),low=low,inverse_count=inverse_count,sum_count=sum_count,
                           component_counts=parts,bound=str(bound)))
    return dict(mean=str(v['mean']),critical_moment=str(sum((v['mean']/x)**2 for x in a)/N),
                comparison_inertia=inertia(sub(b,inv)),weak_frequency=list(map(str,ls)),
                density_checks=densities,counts=counts)

def main():
    need(inertia([[Q(0),Q(2)],[Q(2),Q(0)]])==(1,1,0), '2x2 inertia diagnostic')
    need(inertia(diag([1,-2,0]))==(1,1,1), 'scalar inertia diagnostic')
    profiles=[[1]*N,[4]*N,[1]+[9]*(N-1),[1 if x.bit_count()%2 else 4 for x in range(N)]]
    rows=[]; rejected=0
    for a in profiles:
        v=make(a); rows.append(verify(v))
        mutations=[]
        w=copy.deepcopy(v); w['la'][0][0]+=1; mutations.append(w)
        w=copy.deepcopy(v); w['inv'][0][0]+=1; mutations.append(w)
        w=copy.deepcopy(v); w['flows'][0][0][0]+=1; mutations.append(w)
        w=copy.deepcopy(v); w['b'][0][0]-=1; mutations.append(w)
        for w in mutations:
            try: verify(w)
            except ValueError: rejected+=1
            else: raise RuntimeError('Real matrix/inverse/flow mutation accepted')
    need(len(rows)==4 and rejected==16, 'acceptance counters')
    print(json.dumps(dict(status='EXACT_FINITE_ADAPTER_FIXTURES_ACCEPTED',accepted=4,
        real_mutations_rejected=16,optimized=not __debug__,fixtures=rows,
        general_theorem_verified=False,new_lean_run=False,independent_review=False),indent=2))

if __name__=='__main__': main()
