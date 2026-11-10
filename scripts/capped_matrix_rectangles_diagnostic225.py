#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Lluis Eriksson
"""Selected exact finite matrix/refinement checks. Owned Colab Linux only.
No all-size scalar partition replay, formal proof or novelty claim. No assert gates.
"""
from fractions import Fraction as F
from itertools import product
import json,random

def require(v,m):
 if not v:raise ValueError(m)
def columns(r,variant):
 Q=[[F(int(i==j)) for j in range(r)] for i in range(r)]
 for step in range(r+1):
  a=step%r;b=(step+1+variant)%r
  if a==b:b=(b+1)%r
  for i in range(r):
   x,y=Q[i][a],Q[i][b];Q[i][a]=F(3,5)*x+F(4,5)*y;Q[i][b]=-F(4,5)*x+F(3,5)*y
 for a in range(r):
  for b in range(r):require(sum(Q[i][a]*Q[i][b] for i in range(r))==int(a==b),'Exact rotation')
 return Q
def matrix(Q,lam):return [[sum(Q[i][k]*lam[k]*Q[j][k] for k in range(len(lam))) for j in range(len(lam))] for i in range(len(lam))]
def quad(M,v):return sum(v[i]*M[i][j]*v[j] for i in range(len(v)) for j in range(len(v)))
def sites(rect):return product(*(range(a,b) for a,b in rect))
def refinement(D,n,Z):
 rects=[tuple((0,n) for _ in range(D))]
 for z in sorted(Z):
  found=[i for i,R in enumerate(rects) if all(a<=t<b for (a,b),t in zip(R,z))];require(len(found)==1,'Unique rectangle ownership')
  idx=found[0];R=rects[idx]
  if all(b-a==1 for a,b in R):continue
  new=[tuple((t,t+1) for t in z)]
  for i,(a,b) in enumerate(R):
   for low,high in [(a,z[i]),(z[i]+1,b)]:
    if low<high:new.append(tuple((z[j],z[j]+1) if j<i else (low,high) if j==i else R[j] for j in range(D)))
  require(len(new)<=2*D+1,'Point refinement count');rects[idx:idx+1]=new
 own={}
 for R in rects:
  for x in sites(R):own[x]=own.get(x,0)+1
 require(len(own)==n**D and set(own.values())=={1},'Complete disjoint rectangle cover')
 require(len(rects)<=1+2*D*len(Z),'Total count')
 require(all(tuple((t,t+1) for t in z) in rects for z in Z),'Actual singleton isolation')
 return rects
def rows(U,rects,V):
 value=F(0);h=len(next(iter(U.values())))
 for R in rects:
  X=list(sites(R));value+=sum(sum(U[x][j] for x in X)**2 for j in range(h))/F(V*len(X))
 return value
def case(n,h,kind):
 D=4;r=D*h;V=n**D;alpha=F(81,16);sigma=F(9,4);c=F(1);X=list(product(range(n),repeat=D))
 def forward(x,i):
  y=list(x);y[i]=(y[i]+1)%n;return tuple(y)
 origin=(0,)*D;wrap=(n-1,)+(0,)*(D-1)
 I=set() if kind=='none' else set(X) if kind=='all' else {wrap if kind=='wrap' else origin}
 base=[F(10+i) for i in range(r)];bad=base[:]
 for i,v in enumerate([F(-7),F(0),F(1),sigma][:r]):bad[i]=v
 spectra={x:(bad if x in I else base) for x in X};N=sum(sum(l<=sigma for l in spectra[x]) for x in X);T=sigma+1+N
 budget=sum(sum(F(1) if l<=0 else min(F(1),alpha/l**2) for l in spectra[x]) for x in X)
 require(budget==N+alpha*sum(sum(l**-2 for l in spectra[x] if l>sigma) for x in X),'Actual cap equality')
 Z=I|{forward(x,i) for x in I for i in range(D)};rects=refinement(D,n,Z);L=max([T-l for x in X for l in spectra[x] if l<=sigma],default=F(0));K=1+4*D*L
 replacement={x:[T if l<=sigma else l for l in spectra[x]] for x in X};scalar=sum(min(replacement[x])**-2 for x in X)
 require(scalar<=(budget-N)/alpha+1,'Scalar inverse budget')
 cache={}
 def pair(x):
  key=(x in I,sum(x)%2)
  if key not in cache:
   q=columns(r,key[1]);cache[key]=(matrix(q,spectra[x]),matrix(q,replacement[x]))
  return cache[key]
 root=[tuple((0,n) for _ in range(D))];rng=random.Random(225+n+h+len(I));fields=[]
 fields.append({x:tuple(F(1) for _ in range(h)) for x in X})
 for j in range(h):
  for p in [origin,forward(wrap,0),forward(origin,0),wrap]:fields.append({x:tuple(F(int(x==p and j==k)) for k in range(h)) for x in X})
 for _ in range(12):fields.append({x:tuple(F(rng.randint(-3,3)) for _ in range(h)) for x in X})
 offdiag_detected=False;endpoint_detected=False;wrap_detected=False;normalization_detected=False
 for U in fields:
  EA=ET=diag_delta=F(0);norm=sum(sum(v*v for v in U[x]) for x in X)/V
  for x in X:
   du=[U[forward(x,i)][j]-U[x][j] for i in range(D) for j in range(h)];A,AT=pair(x)
   EA+=quad(A,du)/V;ET+=quad(AT,du)/V;diag_delta+=sum(du[j]**2*(AT[j][j]-A[j][j]) for j in range(r))/V
  q0=rows(U,root,V);qr=rows(U,rects,V);point=sum(sum(v*v for v in U[z]) for z in Z)/V
  require(q0<=qr and point<=qr,'Normalized refinement inequality')
  require(ET-EA>=0 and ET-EA<=4*D*L*point,'Full rotated correction/endpoint charge')
  # For these n=1,2,3 profiles, a_T>=9/4 and the nonconstant torus gap>=3
  # makes one whole-domain mean a valid positive-replacement coarse observation.
  # This selected fact does not reimplement the all-size scalar construction222.
  require(ET+q0>=norm,'Selected positive-replacement coarse inequality')
  require(EA+K*qr>=norm,'Actual signed-matrix rectangle coercivity')
  offdiag_detected|=ET-EA>diag_delta
  badpoint=sum(sum(v*v for v in U[z]) for z in I)/V
  endpoint_detected|=ET-EA>4*D*L*badpoint
  nowrap=I|{tuple(x[j]+int(i==j) for j in range(D)) for x in I for i in range(D)}
  nowrappoint=sum(sum(v*v for v in U[z]) for z in nowrap if z in U)/V
  wrap_detected|=kind=='wrap' and ET-EA>4*D*L*nowrappoint
  wrong=F(0)
  for R in rects:
   pts=list(sites(R));wrong+=sum(sum(U[x][j] for x in pts)**2 for j in range(h))/F(V*len(pts)**2)
  normalization_detected|=q0>wrong
 return {'n':n,'h':h,'kind':kind,'N':N,'F':str(budget),'rectangles':len(rects),'fields_checked':len(fields),'full_matrix_offdiagonal_omission_rejected':offdiag_detected,'forward_endpoint_omission_rejected':endpoint_detected,'periodic_endpoint_omission_rejected':wrap_detected,'bare_mean_normalization_mutation_rejected':normalization_detected}
def main():
 cases=[case(n,h,kind) for n,h,kind in [(1,1,'all'),(2,1,'none'),(2,2,'one'),(2,2,'wrap'),(3,1,'one'),(3,2,'wrap'),(2,1,'all')]]
 controls={key:any(x[key] for x in cases) for key in ['full_matrix_offdiagonal_omission_rejected','forward_endpoint_omission_rejected','periodic_endpoint_omission_rejected','bare_mean_normalization_mutation_rejected']}
 require(all(controls.values()),'A preregistered actual matrix/field mutation was not rejected')
 print(json.dumps({'status':'SELECTED_EXACT_MATRIX_REFINEMENT_DIAGNOSTICS_CHECKED','D':4,'P':2,'alpha':'81/16','sigma':'9/4','cases':cases,'negative_controls':controls,'negative_controls_rejected':sum(controls.values()),'scope':'Seven finite rational original-start matrix families; actual rotated direction/internal channels and wraps. Uses one coarse root mean only in selected small tori where its positive gap is known. Not all-size222construction replay, machine proof, independent reproduction, novelty finding or physical theorem.'},sort_keys=True,indent=2))
if __name__=='__main__':main()
