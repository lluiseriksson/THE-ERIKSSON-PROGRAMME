import json
from fractions import Fraction as F

# Exact polynomial coefficients in (m,x,y,delta,K), not point sampling.
N = 5
ZERO = (0,) * N

def clean(p):
    return {a: b for a, b in p.items() if b}

def add(*ps):
    out = {}
    for p in ps:
        for a, b in p.items():
            out[a] = out.get(a, F(0)) + b
    return clean(out)

def scale(c, p):
    return clean({a: F(c) * b for a, b in p.items()})

def mul(p, q):
    out = {}
    for a, b in p.items():
        for c, d in q.items():
            e = tuple(a[i] + c[i] for i in range(N))
            out[e] = out.get(e, F(0)) + b * d
    return clean(out)

def sq(p):
    return mul(p, p)

def const(c):
    return {ZERO: F(c)} if c else {}

def var(i):
    a = [0] * N
    a[i] = 1
    return {tuple(a): F(1)}

def sub(p, q):
    return add(p, scale(-1, q))

def require(ok, msg):
    if not ok:
        raise ValueError(msg)

m, x, y, delta, K = [var(i) for i in range(N)]
c = F(19, 5)
threshold = F(1138, 35)
u = [add(m,x,scale(F(1,2),delta)),
     add(m,scale(-1,x),scale(F(1,2),delta)),
     add(m,y,scale(F(-1,2),delta)),
     add(m,scale(-1,y),scale(F(-1,2),delta))]
alpha = [1,6,4,1]
E = add(*(scale(alpha[i],sq(sub(u[(i+1)%4],u[i]))) for i in range(4)))
norm = add(*(sq(a) for a in u))
O = scale(F(1,2),add(sq(add(u[0],u[1])),sq(add(u[2],u[3]))))
actual = add(E,mul(K,O),scale(-c,norm))
X = sub(x,scale(F(25,2),delta))
Y = add(y,scale(F(75,14),delta))

def proposed(t=threshold, cross=F(35,17), mode=F(4)):
    return add(scale(mode,mul(sub(K,const(c)),sq(m))),
               scale(F(17,5),sq(add(X,scale(cross,Y)))),
               scale(F(84,85),sq(Y)),
               mul(sub(K,const(t)),sq(delta)))

def evaluate(p, values):
    out=F(0)
    for powers, coefficient in p.items():
        term=coefficient
        for value, power in zip(values,powers):
            term *= F(value) ** power
        out += term
    return out

def check():
    accepted=0
    require(actual == proposed(), 'universal coefficient identity differs')
    accepted+=1
    require(norm == add(scale(4,sq(m)),scale(2,sq(x)),scale(2,sq(y)),sq(delta)), 'norm decomposition')
    require(O == add(scale(4,sq(m)),sq(delta)), 'full observation decomposition')
    accepted+=1
    require(scale(F(1,4),add(*u))==m and
            scale(F(1,2),sub(u[0],u[1]))==x and
            scale(F(1,2),sub(u[2],u[3]))==y and
            scale(F(1,2),sub(add(u[0],u[1]),add(u[2],u[3])))==delta,
            'decomposition is not invertible')
    accepted+=1
    det=F(17,5)*F(77,5)-49
    r0=(F(77,5)*5-35)/det
    r1=(F(17,5)*5-35)/det
    require(det==F(84,25) and (r0,r1)==(F(25,2),F(-75,14)), 'Schur solve')
    require(5*(r0+r1)==F(250,7) and F(250,7)-F(16,5)==threshold and threshold>c, 'Schur threshold')
    accepted+=1
    values=[0,F(25,2),F(-75,14),1,0]
    witness=[evaluate(a,values) for a in u]
    require(witness==[F(13),F(-12),F(-41,7),F(34,7)], 'actual witness coordinates')
    require(evaluate(E,values)==F(67468,49) and evaluate(norm,values)==F(18174,49) and evaluate(O,values)==1, 'actual witness arithmetic')
    # Evaluate m,x,y,delta but preserve K by checking at two distinct K:
    # residual is degree1 in K because E,norm,O are independent of K.
    require(all(a[4]<=1 for a in actual), 'K degree changed')
    for kval in [F(0),F(1)]:
        values[-1]=kval
        require(evaluate(actual,values)==kval-threshold, 'witness affine defect')
    accepted+=1
    mutations=[proposed(t=threshold+F(1,35)),proposed(cross=F(-35,17)),proposed(mode=F(0))]
    rejected=0
    for j, candidate in enumerate(mutations):
        if candidate==actual:
            raise ValueError('accepted actual polynomial mutation '+str(j))
        rejected+=1
    require(accepted==5 and rejected==3, 'counter mismatch')
    return {'status':'EXACT_COEFFICIENT_IDENTITY_AND_WITNESS_VERIFIED',
            'accepted':accepted,'real_mutations_rejected':rejected,
            'variables':['m','x','y','delta','K'],
            'actual_nonzero_monomials':len(actual),
            'threshold':str(threshold),'target':str(c),
            'witness':[str(a) for a in witness],
            'method':'Universal exact rational polynomial coefficient comparison, not sampling',
            'Lean_verified':False,'independent_authorship':False,
            'all_physical_dimensions':'Paper transport; not executed by this scalar checker'}

if __name__=='__main__':
    print(json.dumps(check(),sort_keys=True))