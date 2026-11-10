#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Lluis Eriksson
"""Selected exact sparse diagonal-matrix and partition-rank checks. Colab only.
Normalized rows differ from integer incidence rows by nonzero scalar factors;
rank/kernel checks use that exact invariance, not rounded square roots.
"""
from fractions import Fraction as F
from itertools import product
import json,random

def require(v,m):
 if not v:raise ValueError(m)
def rank(A):
 rows=[[F(x) for x in row] for row in A];pivot=0
 if not rows:return 0
 for j in range(len(rows[0])):
  found=next((i for i in range(pivot,len(rows)) if rows[i][j]),None)
  if found is None:continue
  rows[pivot],rows[found]=rows[found],rows[pivot];value=rows[pivot][j];rows[pivot]=[x/value for x in rows[pivot]]
  for i in range(len(rows)):
   if i!=pivot:
    value=rows[i][j];rows[i]=[x-value*y for x,y in zip(rows[i],rows[pivot])]
  pivot+=1
  if pivot==len(rows):break
 return pivot
def case(m,h):
 D=4;P=2;c=F(1);alpha=F(81,16);sigma=F(9,4);n=3*m+3;V=n**D;r=D*h;M=r*V;a0=min(F(1,8*D),sigma/2);H=sigma*M
 centers=[(3*j+1,)+(1,)*(D-1) for j in range(m)]
 def shift(x,i,delta):
  out=list(x);out[i]=(out[i]+delta)%n;return tuple(out)
 weak={(start,i,0) for x in centers for i in range(D) for start in [x,shift(x,i,-1)]}
 require(len(weak)==2*D*m,'Direction-labelled weak channel count')
 # Explicitly enumerate every local diagonal eigenchannel in each finite profile.
 counted_weak=counted_strong=0
 for x in product(range(n),repeat=D):
  for i in range(D):
   for k in range(h):
    if (x,i,k) in weak:counted_weak+=1
    else:counted_strong+=1
 require(counted_weak==len(weak) and counted_weak+counted_strong==M,'Full channel enumeration')
 cap_weak=min(F(1),alpha/a0**P);cap_strong=min(F(1),alpha/H**P);budget=counted_weak*cap_weak+counted_strong*cap_strong
 require(cap_weak==1 and cap_strong==F(1,M**P),'Actual cap values')
 require(2*D*m<=budget<=2*D*m+1,'Full budget including strong tail')
 def energy(t,omit_incoming=False):
  values={x:F(v) for x,v in zip(centers,t) if v}
  starts=set(values)|{shift(x,i,-1) for x in values for i in range(D)};out=F(0)
  for x in starts:
   for i in range(D):
    delta=values.get(shift(x,i,1),F(0))-values.get(x,F(0))
    coeff=a0 if (x,i,0) in weak and (not omit_incoming or x in centers) else H
    out+=coeff*delta**2
  return out
 fields=0;rng=random.Random(227+m+h)
 for t in [[int(j==i) for j in range(m)] for i in range(m)]+[[rng.randint(-4,4) for _ in range(m)] for _ in range(8)]:
  norm=sum(F(x)**2 for x in t);require(energy(t)==2*D*a0*norm and energy(t)<=norm/4,'Actual complete lowspace energy');fields+=1
 require(energy([1]+[0]*(m-1),True)>F(1,4),'Omitted incoming assignment mutation must be rejected')
 mutated_budget=M*min(F(1),alpha/(sigma/2)**P);require(mutated_budget>2*D*m+1,'Weakening entire strong tail must violate budget')
 partitions=kernel_witnesses=0;hrows_overcount_rejected=False
 for q in range(1,m+1):
  # q-1 initial width-three slabs, and one final slab covering the rest.
  cuts=[3*j for j in range(q)]+[n];rects=[((cuts[j],cuts[j+1]),)+((0,n),)*(D-1) for j in range(q)]
  require(sum((b-a)*n**(D-1) for ((a,b),*_) in rects)==V,'Complete finite slab partition')
  membership=[[int(all(a<=t<b for (a,b),t in zip(R,x))) for x in centers] for R in rects]
  restriction=rank(membership);occupied=sum(any(row) for row in membership)
  require(restriction==occupied and restriction<=q,'Actual restriction rank')
  # Evaluate actual raw full-vector rows on one-point/component fields.
  probes=[(tuple(a for a,b in R),k) for R in rects for k in range(h)]
  full=[[int(k==ell and all(a<=t<b for (a,b),t in zip(R,z))) for z,ell in probes] for R in rects for k in range(h)]
  require(rank(full)==h*q,'Genuine full row rank under nonzero scaling')
  if q<m:
   selected=next(row for row in membership if sum(row)>1);j,k=[i for i,x in enumerate(selected) if x][:2]
   t=[int(i==j)-int(i==k) for i in range(m)]
   require(all(sum(row[i]*t[i] for i in range(m))==0 for row in membership),'Explicit common-partition kernel')
   require(energy(t)<sum(F(x)**2 for x in t),'Actual zero-observation coercivity contradiction');kernel_witnesses+=1
   hrows_overcount_rejected|=h*q>=m and restriction<m
  partitions+=1
 require(h*m>=h*budget/(2*D+1),'Product lower budget relation')
 return {'D':D,'m':m,'h':h,'n':n,'channels_enumerated':M,'weak_channels':counted_weak,'F':str(budget),'lowspace_fields':fields,'partitions':partitions,'actual_kernel_witnesses':kernel_witnesses,'necessary_output_rank':h*m,'ratio_to_h_plus_F':str(F(h*m)/(h+budget)),'incoming_assignment_mutation_rejected':True,'strong_tail_mutation_rejected':True,'overcount_h_lowtests_mutation_rejected':hrows_overcount_rejected}
def main():
 cases=[case(m,h) for m,h in [(1,1),(2,1),(2,2),(3,1),(3,3),(4,1),(4,4)]]
 require(any(x['overcount_h_lowtests_mutation_rejected'] for x in cases),'Actual h-row overcount control missing')
 print(json.dumps({'status':'SELECTED_EXACT_COMMON_PARTITION_RANK_DIAGNOSTICS_CHECKED','cases':cases,'negative_controls_rejected':3,'scope':'Seven finite positive diagonal profilesD4, complete local eigenchannel enumeration and sparse actual original-start lowfields. Integer row rank/kernel checks use exact nonzero normalized row-scaling invariance. Not all-size proof, coexact/physical result, broader channel-adapted impossibility, independent replay or numerical grade.'},sort_keys=True,indent=2))
if __name__=='__main__':main()
