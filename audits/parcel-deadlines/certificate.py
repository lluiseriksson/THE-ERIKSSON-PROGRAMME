"""Certify direct transit lower bounds with nonnegative service and travel."""
from fractions import Fraction as F
from itertools import permutations
from math import lcm
from urllib.request import urlopen
from urllib.parse import quote
from pathlib import Path
from random import Random
from hashlib import sha1,sha256
import json,zipfile,re
import numpy as np
PIN="ecc264d51cae1fb5a3ef85b35b8b7a8c26b2cf47"

def closure(t,service,stops):
    distance=t.copy()
    for k in stops:
        through=distance[:,k,None]+service[k]+distance[k,None,:]
        np.minimum(distance,through,out=distance)
    return distance

def exhaustive_tests():
    rng=Random(22043)
    checked=0
    for n in range(2,8):
        for trial in range(12):
            matrix=np.array([[0 if i==j else rng.randrange(20) for j in range(n)] for i in range(n)])
            service=[rng.randrange(5) for _ in range(n)]
            stops=[k for k in range(n) if rng.random()<0.8]
            dist=closure(matrix,service,stops)
            for p in range(n):
                for d in range(n):
                    if p==d:continue
                    avail=[k for k in stops if k not in (p,d)]
                    best=matrix[p,d]
                    for size in range(1,len(avail)+1):
                        for middle in permutations(avail,size):
                            route=(p,)+middle+(d,)
                            cost=sum(matrix[u,v] for u,v in zip(route,route[1:]))+sum(service[k] for k in middle)
                            best=min(best,cost)
                    assert best==dist[p,d]
                    checked+=1
    return checked

checks=exhaustive_tests()
tree=json.load(urlopen("https://api.github.com/repos/25023189-bit/Integrated-Passenger-and-Parcel-Transportation-SOICT-2026/git/trees/"+PIN+"?recursive=1"))["tree"]
inputs=[v for v in tree if re.fullmatch(r"data/[0-9]+ [0-9]+ [0-9]+\.txt",v["path"])]
if len(inputs)!=9:raise ValueError("practice inputs")
reports=[]
for entry in inputs:
    with urlopen("https://raw.githubusercontent.com/25023189-bit/Integrated-Passenger-and-Parcel-Transportation-SOICT-2026/"+PIN+"/"+quote(entry["path"])) as stream:raw=stream.read()
    if sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()!=entry["sha"]:raise ValueError("blob identity")
    vals=" ".join(line.split("#")[0] for line in raw.decode("utf-8-sig").splitlines()).split()
    it=iter(vals);K,N,M=[int(next(it)) for _ in range(3)]
    cap=[(int(next(it))-1,F(next(it))) for _ in range(K)]
    passengers=[]
    for i in range(N):
        a,b=int(next(it))-1,int(next(it))-1;e,l,sv,rev=[F(next(it)) for _ in range(4)]
        passengers.append((a,b,e,l,sv))
    parcels=[]
    for j in range(M):
        a,b=int(next(it))-1,int(next(it))-1;weight,e,l,ed,ld,sv,rev=[F(next(it)) for _ in range(7)]
        if weight<=0:raise ValueError("positive parcel weights required")
        parcels.append((a,b,weight,e,l,ed,ld,sv))
    V=2*N+2*M+K
    def number(x):
        return int(x) if x.isdecimal() else F(x)
    t=[[number(next(it)) for _ in range(V)] for _ in range(V)]
    if min(map(min,t))<0:raise ValueError("negative time")
    if sum(1 for value in it)!=V*V:raise ValueError("cost matrix shape")
    service={}
    for p,d,_,_,sv in passengers:service[p]=service[d]=sv
    for p,d,_,_,_,_,_,sv in parcels:service[p]=service[d]=sv
    assert len(service)==2*(N+M) and set(service).isdisjoint({d for d,_ in cap})
    assert sorted(list(service)+[d for d,_ in cap])==list(range(V))
    assert min(service.values())>=0 and all(t[i][i]==0 for i in range(V))
    scale=1
    for row in t:
        for val in row:
            if not isinstance(val,int):scale=lcm(scale,val.denominator)
    for sv in service.values():scale=lcm(scale,sv.denominator)
    assert scale*(2*max(map(max,t))+max(service.values()))<2**62
    matrix=np.array([[int(val*scale) for val in row] for row in t],dtype=np.int64)
    fees={k:int(v*scale) for k,v in service.items()}
    violations=adjusted=peak=0
    for k in range(V):
        defect=matrix-(matrix[:,k,None]+matrix[k,None,:])
        violations+=int(np.count_nonzero(defect>0))
        peak=max(peak,int(np.max(defect)))
        if k in fees:adjusted+=int(np.count_nonzero(defect>fees[k]))
    distance=closure(matrix,fees,sorted(fees))
    tested=[]
    for p,d,w,*_ in parcels:
        fits=sum(w<=c for _,c in cap)
        tested.append(dict(p=p+1,d=d+1,direct=int(matrix[p,d]),lower=int(distance[p,d]),admissible_taxis=fits))
    reports.append(dict(path=entry["path"],git_blob=entry["sha"],sha256=sha256(raw).hexdigest(),
        scale=scale,vertices=V,ordered_triangle_violations=violations,worst_raw_defect=peak,
        service_adjusted_violations=adjusted,parcels=tested))
dest=Path("/content/archive.zip")
with zipfile.ZipFile(dest,"w",zipfile.ZIP_DEFLATED) as z:
    z.writestr("certificate.json",json.dumps(dict(pin=PIN,enumerated_pairs=checks,instances=reports),indent=2)+"\n")
print("archive_sha256",sha256(dest.read_bytes()).hexdigest())
