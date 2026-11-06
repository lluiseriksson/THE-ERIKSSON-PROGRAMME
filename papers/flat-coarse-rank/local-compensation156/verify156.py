"""Own Colab only: exact actual finite fields, shifts, stencils and negative Gram forms."""
from itertools import product
from collections import defaultdict
from fractions import Fraction as F
import json,argparse,pathlib,hashlib

def need(ok,msg):
 if not ok:raise ValueError(msg)
def clean(d):return {k:v for k,v in d.items() if v}
def sh(x,i,v,n):
 a=list(x);a[i]=(a[i]+v)%n;return tuple(a)
def packet(n,D,t):
 A=defaultdict(int)
 for u in product((1,2),repeat=D):
  x=tuple(t[i]+u[i] for i in range(D));v=u[0]*u[1]
  A[(x,0)]+=v;A[(sh(x,1,1,n),0)]-=v
  A[(x,1)]-=v;A[(sh(x,0,1,n),1)]+=v
 return clean(A)
def derivatives(A,n,D):
 g=defaultdict(int);div=defaultdict(int)
 for (x,j),v in A.items():
  div[x]+=v;div[sh(x,j,1,n)]-=v
  for i in range(D):g[(x,i,j)]-=v;g[(sh(x,i,-1,n),i,j)]+=v
 return clean(g),clean(div)
def rho(x,R):
 r=tuple(v%6 for v in x)
 return 1 if all(v<4 for v in r) and r!=(1,)*len(x) else R

def metrics(A,n,D,R):
 g,div=derivatives(A,n,D);sites={x for x,i,j in g};L=O=Lw=Ow=Sw=curl=repair=0
 means=[sum(v for (x,j),v in A.items() if j==i) for i in range(D)]
 for (x,i,j),v in g.items():
  rr=rho(x,R);z=v*v;coef=n*n*rr*(2 if i!=j else -1);repair+=(coef-1)*z
  if i==j:L+=z;Lw+=rr*z
  else:O+=z;Ow+=rr*z
 for x in sites:
  for i in range(D):
   for j in range(i+1,D):
    gij=g.get((x,i,j),0);gji=g.get((x,j,i),0)
    Sw+=rho(x,R)*(gij+gji)**2;curl+=(gij-gji)**2
 V=sum(v*v for v in div.values());T=L+O;Q=n*n*(2*Ow-Lw)
 need(curl+V==T,'literal Hodge curl-div cancellation failed')
 need(T+repair==Q,'actual Hodge-plus-gradient repair mismatch')
 positive=n*n*(Ow+Lw);need(positive>=n*n*T,'same-margin positive control comparison failed')
 return {'norm':sum(v*v for v in A.values()),'means':means,'divergence_nonzero':len(div),'L':L,'O':O,'weighted_L':Lw,'weighted_O':Ow,'weighted_S':Sw,'weighted_identity_defect':Sw-Ow+Lw,'Q':Q,'H0':T,'positive_control_energy':positive,'gradient_sites':len(sites),'field_sites':len({x for x,j in A})}

def validate_one(n,D,t,R=None,mutate_field=False):
 R0=(60*D-16)*2**(D-2)+2;R=R0 if R is None else R
 A=packet(n,D,t)
 if mutate_field:
  x=tuple(t[i]+1 for i in range(D));A[(x,0)]=A.get((x,0),0)+1
 r=metrics(A,n,D,R);need(not r['divergence_nonzero'] and not any(r['means']),'field is not actual physical/mean-zero')
 need(r['Q']<0,'actual negative energy required; zero/positive packet rejected')
 need(r['norm']==60*2**(D-2),'packet norm mismatch')
 need(r['L']==72*2**(D-2) and r['O']==(60*D+20)*2**(D-2),'literal derivative totals differ')
 need(r['Q']==-2*n*n,'exact negative energy mismatch')
 need(r['weighted_O']==r['O'] and r['weighted_L']==r['L']+2*(R-1),'coefficient support mismatch')
 need(r['weighted_identity_defect']==2*(R-1),'weighted cancellation defect mismatch')
 g,_=derivatives(A,n,D);E={tuple(t[i]+u[i] for i in range(D)) for u in product(range(4),repeat=D)}
 need({x for x,i,j in g}<=E,'gradient escaped its actual tile envelope')
 return A,r

def disjoint(fields,n,D):
 starts=set();fieldsites=set()
 for A in fields:
  g,_=derivatives(A,n,D);ss={x for x,i,j in g};fs={x for x,j in A}
  need(not starts.intersection(ss),'actual gradient stencils overlap')
  need(not fieldsites.intersection(fs),'actual field supports overlap')
  starts.update(ss);fieldsites.update(fs)
 return len(starts),len(fieldsites)

def case(D,s):
 n=6*s;R=(60*D-16)*2**(D-2)+2;fields=[];rows=[]
 for k in product(range(s),repeat=D):
  t=tuple(6*x for x in k);A,r=validate_one(n,D,t);fields.append(A);rows.append(r)
 need(len(fields)==s**D,'packet count')
 gs,fs=disjoint(fields,n,D)
 combo=defaultdict(int);squares=0
 for j,A in enumerate(fields):
  u=(j%3)-1;squares+=u*u
  for key,v in A.items():combo[key]+=u*v
 combined=metrics(clean(combo),n,D,R)
 need(squares>0 and combined['Q']==-2*n*n*squares and combined['norm']==60*2**(D-2)*squares,'actual negative Gram combination mismatch')
 need(not combined['divergence_nonzero'] and not any(combined['means']),'combination left physical/mean-zero space')
 cell=[rho(x,R) for x in product(range(6),repeat=D)];avg=F(sum(cell),6**D)
 expected=F(R*(6**D-4**D+1)+(4**D-1),6**D)
 need(avg==expected and min(cell)==1 and max(cell)==R and R<2*avg,'positive margin cap/mean failed')
 return {'D':D,'s':s,'n':n,'R_D':R,'mean_rho':[avg.numerator,avg.denominator],'profile_low_vertices':cell.count(1),'profile_high_vertices':cell.count(R),'negative_packets':len(fields),'negative_rayleigh':[-n*n,30*2**(D-2)],'gradient_sites_disjoint':gs,'field_sites_disjoint':fs,'packets':rows,'tested_actual_linear_combination':combined,'combination_coefficient_square_sum':squares,'analytic_inverse_moment_bound':'mean((mu/eta)^r)<=R_D^r for every fixedr>0; no floating approximation'}

def run():
 cases=[case(D,s) for D in (2,3,4) for s in (1,2)];reject=[]
 def wrong_pack():
  n=12;D=3;return disjoint([packet(n,D,(0,0,0)),packet(n,D,(1,0,0))],n,D)
 for label,fn in [
  ('actual-field-changed-at-peak',lambda:validate_one(6,3,(0,0,0),mutate_field=True)),
  ('actual-contrast-lowered-to-zero-energy-threshold',lambda:validate_one(6,3,(0,0,0),R=(60*3-16)*2+1)),
  ('actual-packed-field-shifted-into-overlap',wrong_pack)]:
  try:fn()
  except ValueError as e:reject.append({'mutation':label,'rejected':True,'reason':str(e)})
  else:raise ValueError('accepted actual mutation '+label)
 total=sum(c['negative_packets'] for c in cases)
 need(len(cases)==6 and total==31 and len(reject)==3,'suite counts')
 return {'status':'EXACT_NEGATIVE_BAND_DIAGNOSTICS_PASS','cases':cases,'accepted_cases':6,'total_actual_negative_packets':31,'actual_mutations_rejected':reject,'scope':'finite actual fixtures only; all-n,D theorem is analytic, not Lean or independent review','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',required=True);a=p.parse_args();r=run();pathlib.Path(a.out).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(json.dumps({'status':r['status'],'cases':6,'negative_packets':31,'actual_mutations_rejected':3}))