"""Exact finite fixtures for the supplied-cube construction; Colab Linux ONLY.
This certifies the listed finite certificates, not the general theorem or a gap.
"""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
from math import ceil, prod
import argparse, copy, hashlib, json

class Reject(ValueError):
    pass

def need(ok, message):
    if not ok:
        raise Reject(message)

def packed(b):
    return [[str(l), str(h)] for l,h in b]

def box(raw):
    b=tuple((F(l),F(h)) for l,h in raw)
    need(all(l<h for l,h in b),'empty real box')
    return b

def key(b):
    return tuple(b)

def inside_point(p,b):
    return all(l<x<h for x,(l,h) in zip(p,b))

def proper(a,b):
    return all(max(l,x)<min(h,y) for (l,h),(x,y) in zip(a,b))

def closed_contact(a,b):
    return all(max(l,x)<=min(h,y) for (l,h),(x,y) in zip(a,b))

def corners(b):
    return list(product(*[(l,h) for l,h in b]))

def problem(d,n,clusters):
    return {'D':d,'n':n,'clusters':[{'b':list(b),'L':L} for b,L in clusters]}

def setup(p):
    d,n=p['D'],p['n']
    need(isinstance(d,int) and d>=1 and isinstance(n,int) and n>=1,'domain')
    integer=[]; solids=[]
    for c in p['clusters']:
        b,L=c['b'],c['L']
        need(len(b)==d and isinstance(L,int) and L>=1,'cluster size')
        need(all(isinstance(x,int) and 0<=x and x+L<=n for x in b),'cluster outside root')
        integer.append(tuple((x,x+L) for x in b))
        solids.append(tuple((F(x)-F(1,4),F(x+L)-F(3,4)) for x in b))
    for a,b in combinations(integer,2):need(not proper(a,b),'overlapping integer clusters')
    for a,b in combinations(solids,2):need(not closed_contact(a,b),'solid disjointness')
    vertices=set(v for q in solids for v in corners(q))
    need(len(vertices)==2**d*len(solids),'corner cardinality')
    return d,n,integer,solids,vertices,tuple((F(-1),F(n)) for _ in range(d))

def build(p):
    d,n,integer,solids,vertices,root=setup(p)
    leaves=[]; events=[]
    def visit(c):
        pts=[v for v in vertices if inside_point(v,c)]
        if not pts:
            leaves.append(c);return
        need(len(events)<20000,'fixture event cap')
        side=c[0][1]-c[0][0]
        need(all(h-l==side for l,h in c),'active cell must be cube')
        mids=[(l+h)/2 for l,h in c]
        onplane=any(any(x==m for x,m in zip(v,mids)) for v in pts)
        codes={tuple(int(x>m) for x,m in zip(v,mids)) for v in pts}
        if not onplane and len(codes)==1:
            bits=next(iter(codes))
            a=max(h-x if bit else x-l for v in pts for x,(l,h),bit in zip(v,c,bits))
            need(0<a<side/2,'shrink extent')
            inner=tuple((h-a,h) if bit else (l,l+a) for (l,h),bit in zip(c,bits))
            cur=list(c);strips=[]
            for i in range(d):
                strip=list(cur)
                strip[i]=(cur[i][0],inner[i][0]) if bits[i] else (inner[i][1],cur[i][1])
                strips.append(tuple(strip));cur[i]=inner[i]
            events.append({'kind':'shrink','box':packed(c),'bits':list(bits),'a':str(a),
                           'children':[packed(v) for v in strips+[inner]]})
            leaves.extend(strips);visit(inner)
        else:
            children=[tuple((m,h) if bit else (l,m) for (l,h),m,bit in zip(c,mids,bits))
                      for bits in product((0,1),repeat=d)]
            events.append({'kind':'midpoint','box':packed(c),'children':[packed(v) for v in children]})
            for child in children:visit(child)
    visit(root)
    rects=[]
    for parent,c in enumerate(leaves):
        meet=[q for q in solids if proper(c,q)]
        axes=[]
        for i,(l,h) in enumerate(c):
            cuts=sorted({l,h}|{x for q in meet for x in q[i] if l<x<h})
            axes.append(list(zip(cuts,cuts[1:])))
        for raw in product(*axes):
            lo=[max(0,ceil(l)) for l,h in raw];hi=[min(n,ceil(h)) for l,h in raw]
            if not all(l<h for l,h in zip(lo,hi)):continue
            # Builder labels only one representative. Validator checks the WHOLE rectangle.
            label=next((k for k,q in enumerate(integer) if all(l<=x<h for x,(l,h) in zip(lo,q))),-1)
            rects.append({'lo':lo,'hi':hi,'label':label,'parent':parent})
    return {'problem':p,'events':events,'first_leaves':[packed(c) for c in leaves],'rectangles':rects}

def validate(p,cert):
    d,n,integer,solids,vertices,root=setup(p)
    need(cert['problem']==p,'problem binding')
    leaves=[box(v) for v in cert['first_leaves']]
    need(len(set(leaves))==len(leaves),'duplicate first leaf')
    leafset=set(leaves);eventmap={}
    for e in cert['events']:
        c=box(e['box']);need(c not in eventmap,'duplicate event');eventmap[c]=e
    used_e=set();used_l=set();potential=[];mids_seen=0;shrinks_seen=0
    def inspect(c):
        nonlocal mids_seen,shrinks_seen
        pts=[v for v in vertices if inside_point(v,c)]
        if c not in eventmap:
            need(c in leafset and c not in used_l,'unrepresented/duplicate terminal')
            need(not pts,'terminal contains corner');used_l.add(c);return
        need(c not in used_e and bool(pts),'repeated/empty active event');used_e.add(c)
        e=eventmap[c];children=[box(v) for v in e['children']]
        side=c[0][1]-c[0][0];need(all(h-l==side for l,h in c),'active cube shape')
        mids=[(l+h)/2 for l,h in c]
        if e['kind']=='midpoint':
            expected={tuple((m,h) if bit else (l,m) for (l,h),m,bit in zip(c,mids,bits))
                      for bits in product((0,1),repeat=d)}
            need(len(children)==2**d and set(children)==expected,'midpoint child geometry');mids_seen+=1
        elif e['kind']=='shrink':
            bits=e['bits'];a=F(e['a'])
            need(len(bits)==d and all(v in (0,1) for v in bits) and 0<a<side/2,'shrink parameters')
            need(all(all((x>m if bit else x<m) for x,m,bit in zip(v,mids,bits)) for v in pts),'not common open child')
            inner=tuple((h-a,h) if bit else (l,l+a) for (l,h),bit in zip(c,bits))
            need(all(all(l<=x<=h for x,(l,h) in zip(v,inner)) for v in pts),'shrink loses point')
            need(any(not inside_point(v,inner) for v in pts),'shrink removes no boundary point')
            cur=list(c);expected=[]
            for i in range(d):
                z=list(cur);z[i]=(cur[i][0],inner[i][0]) if bits[i] else (inner[i][1],cur[i][1])
                expected.append(tuple(z));cur[i]=inner[i]
            expected.append(inner)
            need(children==expected,'shrink slab geometry');shrinks_seen+=1
        else:raise Reject('unknown split kind')
        counts=[sum(inside_point(v,child) for v in vertices) for child in children]
        lost=len(pts)-sum(counts);active=sum(v>0 for v in counts)
        need(lost>=0 and 2*lost+active-1>=1,'nondecreasing active potential')
        potential.append(2*lost+active-1)
        for child in children:inspect(child)
    inspect(root)
    need(used_e==set(eventmap) and used_l==leafset,'extraneous certificate cells')
    J=len(solids);N=len(vertices);TD=2**(2*d-1)
    need(sum(potential)==(2*N-1 if J else 0),'potential telescoping')
    if J:
        need(len(eventmap)<=2*N-1,'event count bound')
        need(len(leaves)<=1+(2*N-1)*(2**d-1),'first leaf bound')
    else:need(len(leaves)==1 and not eventmap,'empty scene root')
    occupancy=[sum(proper(c,q) for q in solids) for c in leaves]
    need(all(t<=TD for t in occupancy),'proper occupancy bound')
    AD=2**(d+1)*(2**d-1)*(2**(2*d)+1)**d
    rects=cert['rectangles'];need(bool(rects) and len(rects)<=AD*max(1,J),'integer count bound')
    by_parent=[0]*len(leaves);volumes=[]
    for r in rects:
        lo,hi,k,parent=r['lo'],r['hi'],r['label'],r['parent']
        need(len(lo)==len(hi)==d and all(isinstance(x,int) for x in lo+hi),'integer rectangle type')
        need(all(0<=l<h<=n for l,h in zip(lo,hi)),'empty/outside integer rectangle')
        need(isinstance(parent,int) and 0<=parent<len(leaves),'invalid parent')
        need(all(ceil(l)<=x and y<=ceil(h) for x,y,(l,h) in zip(lo,hi,leaves[parent])),'integer parent ownership')
        hits=[j for j,q in enumerate(integer) if all(max(l,x)<min(h,y) for l,h,(x,y) in zip(lo,hi,q))]
        if k==-1:need(not hits,'outside label crosses cluster')
        else:
            need(isinstance(k,int) and 0<=k<J and hits==[k],'cluster label')
            need(all(x<=l and h<=y for l,h,(x,y) in zip(lo,hi,integer[k])),'not contained in cluster')
        by_parent[parent]+=1;volumes.append(prod(h-l for l,h in zip(lo,hi)))
    need(all(v<=(2*t+1)**d for v,t in zip(by_parent,occupancy)),'facet refinement bound')
    if n**d<=10000:
        seen=set()
        for r in rects:
            for v in product(*[range(l,h) for l,h in zip(r['lo'],r['hi'])]):
                need(v not in seen,'duplicate integer ownership');seen.add(v)
        need(len(seen)==n**d,'integer root not covered');coverage='enumeration'
    else:
        need(sum(volumes)==n**d,'integer volume coverage')
        for a,b in combinations(rects,2):
            need(not all(max(l,x)<min(h,y) for l,h,x,y in zip(a['lo'],a['hi'],b['lo'],b['hi'])),'integer overlap')
        coverage='disjoint-count'
    return {'events':len(eventmap),'first_leaves':len(leaves),'rectangles':len(rects),
            'max_proper_occupancy':max(occupancy,default=0),'midpoint_events':mids_seen,
            'shrink_events':shrinks_seen,'coverage':coverage,'potential_decrease':sum(potential)}

def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def sha(x):return hashlib.sha256(canonical(x)).hexdigest()
def save(p,x):p.write_bytes(canonical(x)+b'\n')

def cases():
    return [
      ('empty',problem(3,4,[])),('singleton-root',problem(3,1,[((0,0,0),1)])),
      ('small-offset',problem(3,7,[((0,0,0),1),((5,5,5),1),((3,1,4),1)])),
      ('adjacent-solids',problem(3,5,[((0,0,0),2),((2,0,0),2),((0,2,0),2),((2,2,2),2)])),
      ('mixed-scales',problem(3,8,[((0,0,0),3),((4,0,0),2),((1,5,1),2),((7,7,7),1)])),
      ('anisotropic-placement',problem(3,6,[((i,2,3),1) for i in range(6)])),
      ('four-dimensional',problem(4,4,[((0,0,0,0),2),((2,2,2,2),2),((0,3,1,2),1)])),
      ('large-root-small-scene',problem(3,10**9,[((0,0,0),1),((10**9-2,1,1),1)])),
    ]

def run(out):
    out.mkdir(exist_ok=False);rows=[];rejects=0;total_mutants=0;mid=0;shrink=0
    for name,p in cases():
        cert=json.loads(canonical(build(p)));row=validate(p,cert);row.update(name=name,certificate_sha256=sha(cert));rows.append(row)
        mid+=row['midpoint_events'];shrink+=row['shrink_events'];save(out/(name+'.json'),cert)
        mutants=[]
        m=copy.deepcopy(cert);m['rectangles'].pop();mutants.append(('drop-cell',m))
        m=copy.deepcopy(cert);m['rectangles'].append(copy.deepcopy(m['rectangles'][0]));mutants.append(('duplicate-cell',m))
        m=copy.deepcopy(cert);m['rectangles'][0]['hi'][0]=m['rectangles'][0]['lo'][0];mutants.append(('collapse-bound',m))
        m=copy.deepcopy(cert);target=next((r for r in m['rectangles'] if r['label']>=0),m['rectangles'][0]);target['label']=-1 if target['label']>=0 else 0;mutants.append(('wrong-cluster-label',m))
        m=copy.deepcopy(cert);m['first_leaves'].pop();mutants.append(('drop-real-leaf',m))
        if cert['events']:
            m=copy.deepcopy(cert);m['events'][0]['children'][0][0][1]=m['events'][0]['children'][0][0][0];mutants.append(('corrupt-split-geometry',m))
        for mutation,m in mutants:
            total_mutants+=1;save(out/(name+'--'+mutation+'.json'),m)
            try:validate(p,m)
            except Reject:rejects+=1
            else:raise RuntimeError('Accepted real mutation '+name+'/'+mutation)
    invalid=[problem(3,4,[((0,0,0),2),((1,1,1),2)]),problem(3,4,[((3,0,0),2)])]
    bad_input_rejects=0
    for i,p in enumerate(invalid):
        save(out/('bad-input-'+str(i)+'.json'),p)
        try:build(p)
        except Reject:bad_input_rejects+=1
        else:raise RuntimeError('Invalid cluster input accepted')
    controls=[]
    for d in (2,3,4):
        K=2**d+1;eps=F(1,4*K+4);C=tuple((F(0),F(1)) for _ in range(d))
        qs=[ ((-eps,F(0)), ((2*j+1)*eps,(2*j+2)*eps)) + tuple((eps,2*eps) for _ in range(d-2)) for j in range(K)]
        need(all(not inside_point(v,C) for q in qs for v in corners(q)),'contact guard vertices')
        need(all(not closed_contact(a,b) for a,b in combinations(qs,2)),'contact guard disjointness')
        closed=sum(closed_contact(q,C) for q in qs);opened=sum(proper(q,C) for q in qs)
        need(closed==K>2**d and opened==0,'closed-contact negative control')
        controls.append({'D':d,'K':K,'closed_contacts':closed,'proper_contacts':opened})
    need(len(rows)==len(cases()) and rejects==total_mutants and rejects>0,'actual fixture counters')
    need(bad_input_rejects==2 and mid>0 and shrink>0 and len(controls)==3,'coverage counters')
    report={'status':'FIXTURES_PASS','scope':'Only listed finite rational certificates; not a universal theorem/Lean/physical certificate',
            'cases':rows,'certificates_accepted':len(rows),'actual_mutations_rejected':rejects,
            'actual_mutations_tested':total_mutants,'bad_inputs_rejected':bad_input_rejects,'closed_contact_controls':controls}
    save(out/'result.json',report);print(json.dumps(report,sort_keys=True))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',required=True);a=p.parse_args();run(Path(a.out))
