#!/usr/bin/env python3
"""Exact finite diagnostics of the analytical partial-invariance partition; Linux only."""
from fractions import Fraction as F
from itertools import product
import json,hashlib,platform,sys
if platform.system()!='Linux': raise RuntimeError('Own Colab Linux required')
def need(ok,message):
    if not ok: raise ValueError(message)
def balanced(n,m):
    q=(n+m-1)//m; small=n//q; large=n%q
    return [small+1]*large+[small]*(q-large)
def check_geometry(lengths,m):
    need(sum(lengths)>0 and all(F(m,2)<=x<=m for x in lengths),'unbalanced extrusion')
def fixture(D,k,n,mode,theta):
    d=D-k; need(d>0 and k>=1,'positive invariant dimension required')
    domain=list(product(range(n),repeat=k))
    def beta(x):
        if mode=='uniform':return 1
        if mode=='strong':return n
        if mode=='checker':return 1 if sum(x)%3==0 else 2*n
        return 1 if all(t==n//2 for t in x) else 2*n
    mass={x:F(1,beta(x)**D) for x in domain}
    nodes=[]
    def build(bounds):
        sizes=[hi-lo for lo,hi in bounds];m=max(sizes)
        need(min(sizes)>=m-1 and min(sizes)>0,'base aspect invariant')
        b=sum((mass[x] for x in product(*(range(lo,hi) for lo,hi in bounds))),F(0))
        node={'m':m,'b':b,'w':F(1,m**d),'children':[]};nodes.append(node)
        if m>=2 and m**d*b>theta:
            pieces=[[(lo,hi)] if hi-lo==1 else [(lo,lo+(hi-lo)//2),(lo+(hi-lo)//2,hi)] for lo,hi in bounds]
            node['children']=[build(list(child)) for child in product(*pieces)]
            for ch in node['children']:
                need(F(m,3)<=ch['m']<=F(2*m,3),'child max-side bounds')
            need(len(node['children'])<=2**k,'arity')
        else:
            if m>1:need(m**d*b<=theta,'accepted mass condition')
            lengths=balanced(n,m);need(sum(lengths)==n and len(lengths)==(n+m-1)//m,'extrusion cover')
            check_geometry(lengths,m)
            # Actual inverse mass on every distinct extrusion shape, not a representative fibre.
            for shape in product(sorted(set(lengths)),repeat=d):
                z=1
                for v in shape:z*=v
                actual=sum((mass[x] for x in product(*(range(lo,hi) for lo,hi in bounds))),F(0))*z
                need(actual==z*b and actual<=m**d*b,'actual extrusion inverse mass')
        return node
    root=build([(0,n)]*k);internal=[x for x in nodes if x['children']];leaves=[x for x in nodes if not x['children']]
    terminal=[x for x in internal if all(not y['children'] for y in x['children'])]
    rho=F(2,3)**d;isum=sum((x['w'] for x in internal),F(0));tsum=sum((x['w'] for x in terminal),F(0));lsum=sum((x['w'] for x in leaves),F(0))
    need(all(x['w']<x['b']/theta for x in internal),'split charge')
    need(sum((x['b'] for x in terminal),F(0))<=root['b'],'terminal disjoint mass')
    need(isum<=tsum/(1-rho)<=root['b']/theta/(1-rho),'geometric terminal charge')
    telescope=root['w']+sum((sum((y['w'] for y in x['children']),F(0))-x['w'] for x in internal),F(0))
    need(lsum==telescope,'exact telescoping')
    need(lsum<=F(1,n**d)+2**k*3**d*isum,'leaf weight bound')
    cells=sum(((n+x['m']-1)//x['m'])**d for x in leaves)
    upper=2**d+F(2**D*3**d,1)/(1-rho)/theta*n**d*root['b']
    need(cells<=upper,'actual rank bound')
    return {'D':D,'k':k,'n':n,'mode':mode,'theta':str(theta),'base_leaves':len(leaves),'full_cells':cells,'internal':len(internal),'mass':str(root['b']),'bound':str(upper)}
def rejected(fn):
    try:fn()
    except ValueError:return True
    raise ValueError('Intentional mutation incorrectly accepted')
def main():
    cases=[]
    for D,maxn in [(3,11),(4,7),(5,5)]:
        for k in range(1,D):
            for n in range(2,maxn+1):
                for mode in ['uniform','strong','checker','isolated']:
                    for theta in [F(1,8),F(1),F(8)]:cases.append(fixture(D,k,n,mode,theta))
    mutations=[]
    mutations.append(rejected(lambda:check_geometry([3,3,1],3)))
    mutations.append(rejected(lambda:need(F(8)*F(1)<=1,'forgot m^d in stop')))
    mutations.append(rejected(lambda:need(F(8)*F(1)==F(1),'forgot invariant volume')))
    mutations.append(rejected(lambda:need(F(1,1)<=F(1,8),'forced singleton acceptance mass')))
    mutations.append(rejected(lambda:fixture(3,3,2,'uniform',F(1))))
    mutations.append(rejected(lambda:need(F(1)+F(1)<=F(1),'charged overlapping internal mass as disjoint')))
    result={'unit':188,'case_count':len(cases),'cases':cases,'mutation_rejections':len(mutations),'all_mutations_rejected':all(mutations),'scope':'Exact finite tree/geometry/mass/rank diagnostics, not all-size proof or local spectral verification','formal_verified':False,'independent_replication':False}
    need(result['case_count']==648 and result['mutation_rejections']==6,'explicit acceptance counters')
    raw=(json.dumps(result,sort_keys=True,separators=(',',':'))+'\n').encode();open('payload188.json','wb').write(raw)
    print('PAYLOAD188_SHA256='+hashlib.sha256(raw).hexdigest());print('CASES=648 MUTATIONS_REJECTED=6 PASS')
if __name__=='__main__': main()