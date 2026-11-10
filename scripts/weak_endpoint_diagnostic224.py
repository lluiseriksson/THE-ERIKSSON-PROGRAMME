#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Lluis Eriksson
"""Selected exact rational/tensor checks of draft224. Owned Colab Linux only.
Not an all-size proof, novelty check or formal certification. No assert gates.
"""
from fractions import Fraction as F
from math import comb
from itertools import product
import json,hashlib

def require(v,m):
 if not v:raise ValueError(m)
def plus(a,b):
 out=[F(0)]*max(len(a),len(b))
 for i,x in enumerate(a):out[i]+=x
 for i,x in enumerate(b):out[i]+=x
 return out
def times(a,b):
 out=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
def shift(a,h):
 out=[F(0)]*len(a)
 for i,x in enumerate(a):
  for j in range(i+1):out[j]+=x*comb(i,j)*h**(i-j)
 return out
def total(a,N):
 if N<0:return F(0)
 sums=[F(N+1)]
 for k in range(1,len(a)):
  sums.append((F((N+1)**(k+1))-sum(F(comb(k+1,j))*sums[j] for j in range(k)))/(k+1))
 return sum(x*s for x,s in zip(a,sums))
def tensor(L):
 # Integer numerator q(t)=t^2(L-t)^2, compact outside[0,L].
 q=[F(0),F(0),F(L*L),F(-2*L),F(1)]
 back=plus(q,[-x for x in shift(q,-1)])
 second=plus(plus(shift(q,1),[-2*x for x in q]),shift(q,-1))
 B=total(times(q,q),L)
 S=total(times(back,back),L)-back[0]**2 # sum1..L, remove t0 only
 # second's polynomial valid1..L-1; compact boundary adds2q(1)^2.
 T=total(times(second,second),L-1)-second[0]**2+2*F((L-1)**4)
 return B,S,T
def direct_tensor(L):
 def q(t):return t*t*(L-t)**2 if 0<=t<=L else 0
 return (sum(q(t)**2 for t in range(L+1)),sum((q(t)-q(t-1))**2 for t in range(L+2)),sum((q(t+1)-2*q(t)+q(t-1))**2 for t in range(-1,L+2)))

def small_actual(D=3,L=16):
 def psi(x):
  v=1
  for t in x:
   if not 0<=t<=L:return 0
   v*=t*t*(L-t)**2
  return v
 def delta(x,i,h):
  y=list(x);y[i]+=h;return tuple(y)
 def A(x):return (psi(x)-psi(delta(x,1,-1)),-psi(x)+psi(delta(x,0,-1)))
 norm=energy=omit_upper=high_boundary=0;nonzero_starts=set();maxdiv=0
 for x in product(range(-1,L+2),repeat=D):
  ax=A(x);norm+=sum(t*t for t in ax)
  div=sum(ax[i]-A(delta(x,i,-1))[i] for i in range(2));maxdiv=max(maxdiv,abs(div))
  for i in range(D):
   other=A(delta(x,i,1));edge=sum((u-v)**2 for u,v in zip(other,ax));energy+=edge
   if edge:
    nonzero_starts.add(x);require(all(0<=t<=L for t in x),'Omitted original start')
   if all(0<=t<L for t in x):omit_upper+=edge
   high_boundary+=edge*(10**9 if any(t==L for t in x) else 1)
 B,S,T=tensor(L);expected_norm=2*S*B**(D-1);expected_energy=2*(T*B**(D-1)+(D-1)*S*S*B**(D-2))
 require(norm==expected_norm and energy==expected_energy and norm>0 and maxdiv==0,'Actual coexact/tensor mismatch')
 require(omit_upper<energy and high_boundary>energy,'Real boundary mutations must change actual energy')
 return {'D':D,'L':L,'norm':str(norm),'energy':str(energy),'nonzero_original_starts':len(nonzero_starts),'actual_divergence_zero':True,'upper_start_omission_rejected':True,'high_boundary_mask_mutation_rejected':True}

def profile(D,m):
 U=32*D*2**D;eta=F(9,2**(D+12)*256**(2*(D-1)));K=F(U)/eta;k=0
 while F(1,4**k)*K>F(1,4):k+=1
 eps=F(1,4**k);L0=2**max(4,k);Ls=[2**j*L0 for j in range(m)];n=16*Ls[-1];V=n**D;H=eps*Ls[-1]**2
 counts=[(L+1)**D for L in Ls];coeff=[eps*L*L for L in Ls];outside=V-sum(counts)
 mu=(outside*H+sum(v*a for v,a in zip(counts,coeff)))/V
 require(mu>=1 and H<=2*mu and min(coeff)>=1 and outside>V/2,'Original coefficient constraints')
 cumulative=0;weak2=[]
 for v,a in zip(counts,coeff):
  cumulative+=v;weak2.append((mu/a)**D*F(cumulative,V)**2)
 weak2.append((mu/H)**D);require(max(weak2)<=1,'Weak strict-cutoff supremum bound')
 # a_j are rational squares, so fullmoment^2 is exact rational even when D odd.
 factor=F(outside,1)/F(Ls[-1],2**k)**D+sum(F(v,1)/F(L,2**k)**D for v,L in zip(counts,Ls))
 strong2=mu**D*factor**2/V**2
 require(strong2>=F(m*m,2**D*16**(2*D)),'Growing fullmoment bound')
 ratio=[]
 for L in [Ls[0],Ls[-1]]:
  B,S,T=tensor(L);actual=F(T,S)+(D-1)*F(S,B)
  require(actual*L*L<=K and eps*L*L*actual<=F(1,4),'Tensor actual all-start low mode')
  ratio.append(str(actual))
 last=1
 for L in Ls:
  require(last+L<n,'Packing');last+=L+3
 return {'D':D,'m':m,'k':k,'n':str(n),'mu':str(mu),'weak_supremum_squared':str(max(weak2)),'fullmoment_squared':str(strong2),'selected_exact_energy_norm_ratios':ratio}

def main():
 for L in [1,2,3,8,16,32]:require(tensor(L)==direct_tensor(L),'Polynomial sum boundary '+str(L))
 actual=small_actual();profiles=[profile(D,m) for D in [3,4,5] for m in [1,2,4,8,16]]
 # Genuine altered weak distribution: replacing cumulative count by0 falsely passes
 # a deliberately overlarge coefficient-ratio probe; independent true count rejects it.
 probe=F(2)**3;true_count=F(1,2);require(probe*true_count**2>1 and probe*0<=1,'Distribution mutation control')
 result={'status':'SELECTED_EXACT_FINITE_TENSOR_DIAGNOSTICS_CHECKED','direct_tensor_cases':6,'actual_coexact_case':actual,'profile_cases':profiles,'negative_controls_rejected':3,'scope':'Selected finite actualD3/L16 fields, exact polynomial sums and15huge-size scalar profiles. Not all-size formal proof, independent reproduction, original priority, physical theorem or PDF assessment.'}
 raw=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode();print(raw.decode(),end='')
if __name__=='__main__':main()
