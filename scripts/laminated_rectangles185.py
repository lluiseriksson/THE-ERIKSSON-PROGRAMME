# SPDX-License-Identifier: AGPL-3.0-or-later
"""Selected exact finite controls for185; own Colab Linux only.

Imports only rational matrix/checking helpers from the pinned184 source.
Finite cases do not prove the all-size analytical theorem or originality.
"""
from itertools import product
from math import prod
import hashlib
import json
from green_moment_partition184 import F, need, matrix, psd, Rejected


def tree(alpha, c, variant='actual'):
    nodes = []
    def visit(lo, hi):
        m = hi-lo
        resistance = sum((1/a for a in alpha[lo:hi]), F(0))
        metric = m*resistance
        if variant == 'omit_length':
            metric = resistance
        if variant == 'arithmetic':
            metric = F(m**3, 1)/sum(alpha[lo:hi])
        if variant == 'omit_last':
            metric = m*sum((1/a for a in alpha[lo:hi-1]), F(0))
        node = {'lo':lo,'hi':hi,'m':m,'R':resistance,'children':[]}
        nodes.append(node)
        if m >= 2 and c*metric > 2:
            mid = lo+m//2
            node['children'] = [visit(lo, mid), visit(mid, hi)]
        return node
    visit(0, len(alpha))
    return nodes


def validate_tree(alpha, c, D, nodes):
    n, d = len(alpha), D-1
    leaves = sorted((x for x in nodes if not x['children']), key=lambda x:x['lo'])
    need([i for x in leaves for i in range(x['lo'],x['hi'])] == list(range(n)), 'interval coverage')
    for x in leaves:
        need(x['m'] == x['hi']-x['lo'] and x['m'] >= 1, 'leaf length')
        need(x['m'] == 1 or c*x['m']*sum((1/a for a in alpha[x['lo']:x['hi']]), F(0)) <= 2,
             'actual resistance certificate')
    internal = [x for x in nodes if x['children']]
    terminal = [x for x in internal if all(not y['children'] for y in x['children'])]
    wi = sum((F(1,x['m']**d) for x in internal), F(0))
    wt = sum((F(1,x['m']**d) for x in terminal), F(0))
    ratio = F(2,3)**d
    need(wi <= wt/(1-ratio), 'terminal-ancestor geometric charge')
    wl = sum((F(1,x['m']**d) for x in leaves), F(0))
    need(wl <= F(1,n**d)+2*3**d*wi, 'telescoped leaf cost')
    q = sum(((n+x['m']-1)//x['m'])**d for x in leaves)
    need(q <= (2*n)**d*wl, 'actual transverse mesh count')
    if D == 4:
        B = F(2*6**d,1)/(1-ratio)
        moment = n**d*sum((a**(-2) for a in alpha), F(0))
        need(q <= 2**d+B*(c/2)**2*moment, 'critical full coefficient moment count')
        for x in internal:
            mass = sum((a**(-2) for a in alpha[x['lo']:x['hi']]), F(0))
            need(F(1,x['m']**d) < (c/2)**2*mass, 'derived critical bad-node charge')
    return leaves, q


def boxes(n, D, leaves):
    out = []
    for x in leaves:
        m = x['m']
        bins = [range(i,min(n,i+m)) for i in range(0,n,m)]
        for transversal in product(bins, repeat=D-1):
            out.append(list(product(range(x['lo'],x['hi']),*transversal)))
    return out


def partition_projection(vertices, cells, wrong_volume=False):
    index = {v:i for i,v in enumerate(vertices)}
    seen = []
    p = matrix(len(vertices))
    for cell in cells:
        need(len(cell) > 0 and len(set(cell)) == len(cell), 'cell nonempty and distinct')
        seen.extend(cell)
        for x in cell:
            for y in cell:
                p[index[x]][index[y]] = F(1,len(cell)**(2 if wrong_volume else 1))
    need(len(seen) == len(vertices) and len(set(seen)) == len(vertices), 'full disjoint rectangle cover')
    return p


def laplacian(vertices, n, a, periodic):
    index = {v:i for i,v in enumerate(vertices)}
    l = matrix(len(vertices))
    for x in vertices:
        for j in range(len(x)):
            if not periodic and x[j]+1 == n:
                continue
            y = list(x)
            y[j] = (y[j]+1)%n
            y = tuple(y)
            if y not in index or y == x:
                continue
            u,v = index[x],index[y]
            l[u][u] += a[x]
            l[v][v] += a[x]
            l[u][v] -= a[x]
            l[v][u] -= a[x]
    return l


def verify_global(alpha, D, c):
    n = len(alpha)
    leaves,q = validate_tree(alpha,c,D,tree(alpha,c))
    cells = boxes(n,D,leaves)
    need(len(cells) == q, 'constructed cell count')
    vertices = list(product(range(n),repeat=D))
    a = {x:alpha[x[0]] for x in vertices}
    l = laplacian(vertices,n,a,True)
    p = partition_projection(vertices,cells)
    psd([[l[i][j]+c*p[i][j]-c*F(i==j) for j in range(len(vertices))]
         for i in range(len(vertices))])
    return {'D':D,'n':n,'c':str(c),'alpha':[str(x) for x in alpha],'cells':q,
            'matrix_size':len(vertices)}


def reject(operation):
    try:
        operation()
    except Rejected:
        return
    raise Rejected('intentional mutation accepted')


def wrong_mean_control():
    vertices = list(product(range(2), repeat=3))
    l = laplacian(vertices, 2, {x:F(2) for x in vertices}, True)
    p = partition_projection(vertices, [vertices], wrong_volume=True)
    psd([[l[i][j]+p[i][j]-F(i==j) for j in range(8)] for i in range(8)])


def physical_fibre_falsifier():
    n,D,c=4,3,F(15,2)
    vertices=list(product(range(n),repeat=D))
    z=(1,1,1)
    def shift(x,j,sign):
        y=list(x);y[j]=(y[j]+sign)%n;return tuple(y)
    g={x:F(x==z) for x in vertices}
    u={x:(g[x]-g[shift(x,1,-1)],-g[x]+g[shift(x,0,-1)],F(0)) for x in vertices}
    a={x:F(1 if all(v<=2 for v in x) else 64) for x in vertices}
    mean=[sum(u[x][i] for x in vertices)/len(vertices) for i in range(D)]
    div={x:sum((u[x][i]-u[shift(x,i,-1)][i] for i in range(D)),F(0)) for x in vertices}
    norm=sum((v*v for x in vertices for v in u[x]),F(0))
    grad=F(0);weighted=F(0);curl=F(0)
    for x in vertices:
        for j in range(D):
            for i in range(D):
                delta=u[shift(x,j,1)][i]-u[x][i]
                grad+=delta*delta;weighted+=a[x]*delta*delta
                if delta:
                    need(a[x]==1,'actual gradient start must be weak')
        for i in range(D):
            for j in range(i+1,D):
                v=(u[shift(x,i,1)][j]-u[x][j])-(u[shift(x,j,1)][i]-u[x][i])
                curl+=v*v
    need(all(x==0 for x in mean) and all(x==0 for x in div.values()),'actual mean/divergence')
    need(norm==4 and weighted==28 and curl==grad==28,'actual coexact norm/gradient/Hodge')
    mu=sum(a.values())/len(vertices)
    need(mu==F(2395,64) and all(1<=x<=2*mu for x in a.values()),'original coefficients')
    need(F(27,64)*F(1178,5)+F(37,64)==F(31991,320)<100,'critical moment rigorous upper envelope')
    representative=[a[(i,3,3)] for i in range(n)]
    need(n*sum((1/x for x in representative),F(0))==F(1,4)<2/c,'representative fibre accepted')
    need(weighted<c*norm,'representative extension is actually false on a coexact field')
    return {'n':n,'D':D,'c':str(c),'mu':str(mu),'norm':str(norm),'energy':str(weighted),
            'target':str(c*norm),'zero_backward_divergence':True,'moment_upper_bound':str(F(31991,320))}


def main():
    psd_cases=[]
    for D,alpha,c in [(3,[2,2],F(1)),(3,[4,64,64],F(1)),(3,[1,64,64],F(1)),
                      (3,[1,2,64],F(1,2)),(4,[4,4],F(1)),(4,[2,2],F(1))]:
        psd_cases.append(verify_global(list(map(F,alpha)),D,c))
    tree_cases=[]
    for D in [3,4,5]:
        for n in [2,3,5,8,17,31]:
            for seed in range(4):
                alpha=[F(1+(7*i*i+11*seed+3*i)%97) for i in range(n)]
                c=[F(1,2),F(1),F(3),F(8)][seed]
                leaves,q=validate_tree(alpha,c,D,tree(alpha,c))
                tree_cases.append({'D':D,'n':n,'seed':seed,'cells':q,'interval_leaves':len(leaves)})
    layer_cases=[]
    for D,t in [(3,2),(3,3),(4,2),(4,3),(5,2)]:
        n=t**D;mu=F(n*n);b=F(t**(2*D-2));H=(n*mu-b)/(n-1)
        alpha=[b]+[H]*(n-1)
        leaves,q=validate_tree(alpha,F(1),D,tree(alpha,F(1)))
        need(q==1 and len(leaves)==1 and sum(alpha)/n==mu and H>mu and 1<=b<=mu,
             'fixed-M2 weak-layer positive family')
        need((mu/b)**D == n*n,'exact square of weak critical moment relation')
        layer_cases.append({'D':D,'t':t,'n':n,'b':str(b),'H':str(H),
                            'root_mR':str(n*sum((1/x for x in alpha),F(0))),'cells':q})
    falsifier=physical_fibre_falsifier()
    mutations=[]
    operations=[
        ('lost interval length',lambda:validate_tree([F(1)]*4,F(1),3,tree([F(1)]*4,F(1),'omit_length'))),
        ('arithmetic instead of resistance',lambda:validate_tree([F(1),F(100)],F(4),3,
                                                       tree([F(1),F(100)],F(4),'arithmetic'))),
        ('last start omitted',lambda:validate_tree([F(100),F(1)],F(4),3,
                                                       tree([F(100),F(1)],F(4),'omit_last'))),
        ('wrong normalized mean',wrong_mean_control),
        ('uncovered transverse tail',lambda:partition_projection(list(product(range(3),repeat=3)),
                                                     [list(product(range(3),range(2),range(2)))])),
        ('representative fibre promoted',lambda:need(F(falsifier['energy'])>=F(falsifier['target']),
                                                     'coexact representative-fibre false claim')),
    ]
    for name,op in operations:
        reject(op);mutations.append(name)
    need(len(psd_cases)==6 and len(tree_cases)==72 and len(layer_cases)==5 and len(mutations)==6,
         'explicit acceptance counters')
    result={'status':'SELECTED_EXACT_LAMINATE_CONTROLS','psd_cases':psd_cases,'tree_cases':tree_cases,
            'layer_cases':layer_cases,'coexact_falsifier':falsifier,'mutations_rejected':mutations,
            'limits':'Finite rational cases and adversarial mutations; no all-size computational proof, Lean or independent review.'}
    raw=(json.dumps(result,sort_keys=True,separators=(',',':'))+'\n').encode()
    print(raw.decode(),end='');print('PAYLOAD_SHA256='+hashlib.sha256(raw).hexdigest())


if __name__=='__main__':
    main()
