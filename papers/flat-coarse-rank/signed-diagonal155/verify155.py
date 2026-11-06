"""Own Colab Linux only. Exact finite diagnostics of the analytic proof, not Lean."""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
import argparse,json,hashlib,pathlib,copy

def need(ok,msg):
 if not ok: raise ValueError(msg)
def shift(x,i,step,n):
 y=list(x);y[i]=(y[i]+step)%n;return tuple(y)
def linadd(a,b,sign=1):
 r=dict(a)
 for k,v in b.items():
  r[k]=r.get(k,0)+sign*v
  if not r[k]:del r[k]
 return r
def add_square(poly,form,scale=1):
 items=sorted(form.items())
 for p,(i,v) in enumerate(items):
  for j,w in items[p:]:
   k=(i,j);poly[k]+=scale*v*w*(1 if i==j else 2)
def identity(n,D,wrong_div=False):
 X=list(product(range(n),repeat=D));idx={x:k for k,x in enumerate(X)}
 def diff(x,i,j,back=False):
  if back:return linadd({j*len(X)+idx[x]:1},{j*len(X)+idx[shift(x,i,-1,n)]:1},-1)
  return linadd({j*len(X)+idx[shift(x,i,1,n)]:1},{j*len(X)+idx[x]:1},-1)
 residual=defaultdict(int);monomials=0
 for x in X:
  div={}
  for i in range(D):
   div=linadd(div,diff(x,i,i,back=not wrong_div));add_square(residual,diff(x,i,i),1)
   for j in range(D):
    if i!=j:add_square(residual,diff(x,i,j),-1)
  add_square(residual,div,-1)
  for i in range(D):
   for j in range(i+1,D):add_square(residual,linadd(diff(x,i,j),diff(x,j,i)),1)
 monomials=len(residual);nonzero={k:v for k,v in residual.items() if v}
 need(not nonzero,'literal mixed-square polynomial identity failed')
 return {'n':n,'D':D,'variables':D*len(X),'compared_monomials':monomials,'residual_nonzero':len(nonzero)}
COS={2:[F(1),F(-1)],3:[F(1),F(-1,2),F(-1,2)],4:[F(1),F(0),F(-1),F(0)],6:[F(1),F(1,2),F(-1,2),F(-1),F(-1,2),F(1,2)]}
LAM={2:F(4),3:F(3),4:F(2),6:F(1)}
def field(n,D,kind):
 X=list(product(range(n),repeat=D));f=COS[n];A={x:[F(0)]*D for x in X}
 for x in X:
  if kind=='physical':A[x][0]=f[(x[0]+x[1])%n];A[x][1]=-A[x][0]
  elif kind=='longitudinal':A[x][0]=f[x[0]]
  elif kind=='constant':A[x][0]=F(1)
  elif kind=='curl':
   def psi(y):return F((sum((i+1)*y[i] for i in range(D))**2+3*y[0])%7)
   A[x][0]=psi(x)-psi(shift(x,1,-1,n));A[x][1]=-(psi(x)-psi(shift(x,0,-1,n)))
  else:raise ValueError('unknown field')
 return A

def evaluate(n,D,A,a,kappa,beta=F(0),variable=False,diagonal_mutation=False):
 X=list(A);N=len(X);off=diag=div=sym=q=norm=F(0)
 for x in X:
  norm+=sum(v*v for v in A[x]);dv=F(0)
  for i in range(D):
   dv+=A[x][i]-A[shift(x,i,-1,n)][i]
   for j in range(D):
    v=A[shift(x,i,1,n)][j]-A[x][j]
    base=a if i!=j else -kappa
    coef=base+(F((sum(x)+i+j)%3) if variable else 0)
    if diagonal_mutation and i==j:coef-=1
    need(coef>=base,'actual coefficient bound violated')
    q+=coef*v*v
    if i==j:diag+=v*v
    else:off+=v*v
   for j in range(i+1,D):
    v=A[shift(x,i,1,n)][j]-A[x][j]+A[shift(x,j,1,n)][i]-A[x][i];sym+=v*v
  div+=dv*dv
 means=[sum(A[x][j] for x in X)/N for j in range(D)]
 B=N*sum(v*v for v in means);P=norm-B
 need(sym==off+div-diag,'actual-field mixed identity mismatch')
 need(off+div>=LAM[n]*P,'off-diagonal plus divergence Poincare diagnostic failed')
 need(q+beta*div>=kappa*sym+(a-kappa)*off+(beta-kappa)*div,'actual comparison failed')
 return {'norm':norm,'P':P,'B':B,'off':off,'diag':diag,'div':div,'sym':sym,'q':q,'full':q+beta*div}

def physical_witness(n,D,mutate=False):
 A=field(n,D,'longitudinal' if mutate else 'physical');r=evaluate(n,D,A,F(3),F(1))
 need(r['norm']>0 and r['B']==0 and r['div']==0,'witness not actual mean-zero physical field')
 need(r['q']==2*LAM[n]*r['norm'],'sharp physical energy mismatch')
 return r

def rationalize(v):
 if isinstance(v,F):return [v.numerator,v.denominator]
 if isinstance(v,dict):return {k:rationalize(x) for k,x in v.items()}
 if isinstance(v,list):return [rationalize(x) for x in v]
 return v

def run():
 identities=[identity(n,D) for n in (2,3,4) for D in (2,3)]
 rows=[]
 for n in (2,3,4,6):
  for D in (2,3):
   ph=physical_witness(n,D);c=2*LAM[n]
   zero=evaluate(n,D,field(n,D,'physical'),F(3),F(3));need(zero['q']==0 and zero['div']==zero['B']==0,'critical null witness failed')
   neg=evaluate(n,D,field(n,D,'physical'),F(3),F(4));need(neg['q']==-LAM[n]*neg['norm']<0,'negative physical witness failed')
   lng=evaluate(n,D,field(n,D,'longitudinal'),F(3),F(1),F(3));need(lng['q']==-LAM[n]*lng['norm'] and lng['full']==c*lng['norm'],'longitudinal sharpness failed')
   con=evaluate(n,D,field(n,D,'constant'),F(3),F(1));need(con['q']==0 and con['B']==con['norm']>0,'mean coefficient necessity failed')
   var=evaluate(n,D,field(n,D,'curl'),F(3),F(1),F(3),variable=True);need(var['div']==var['B']==0 and var['q']>=c*var['norm'],'actual variable signed curl test failed')
   rows.append({'n':n,'D':D,'lambda':LAM[n],'physical_sharp':ph,'critical_zero':zero,'negative_physical':neg,'longitudinal':lng,'constant':con,'variable_signed_curl':var})
 rejected=[]
 for name,fn in [
  ('wrong-forward-divergence',lambda:identity(3,2,wrong_div=True)),
  ('physical-field-replaced-by-longitudinal',lambda:physical_witness(4,3,mutate=True)),
  ('actual-diagonal-coefficient-below-lower-bound',lambda:evaluate(4,3,field(4,3,'physical'),F(3),F(1),diagonal_mutation=True))]:
  try:fn()
  except ValueError as e:rejected.append({'mutation':name,'rejected':True,'reason':str(e)})
  else:raise ValueError('accepted actual mutation '+name)
 need(len(identities)==6 and len(rows)==8 and len(rejected)==3,'suite count mismatch')
 return rationalize({'status':'EXACT_FINITE_DIAGNOSTICS_PASS','identity_cases':identities,'witness_cases':rows,'physical_witnesses':8,'witness_kinds_per_case':6,'accepted_identity_cases':6,'accepted_witness_records':48,'actual_mutations_rejected':rejected,'scope':'analytic proof support only; no Lean, all-n execution claim, independent review or general novelty certificate','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()})
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',required=True);args=p.parse_args()
 result=run();pathlib.Path(args.out).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps({'status':result['status'],'identities':6,'witness_records':48,'actual_mutations_rejected':3}))