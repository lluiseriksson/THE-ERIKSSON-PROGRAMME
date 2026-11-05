# Pure exact finite diagnostics. Execute only in exclusive Colab Linux.
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse,json,hashlib,subprocess,sys,os,time,re,zipfile,traceback

def need(ok,msg):
 if not ok:raise ValueError(msg)
def q(x):return (F(x),F(0))
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def neg(x):return (-x[0],-x[1])
def sub(x,y):return add(x,neg(y))
def mul(x,y):return (x[0]*y[0]+85*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def scale(x,t):return (x[0]*t,x[1]*t)
def inv(x):
 den=x[0]**2-85*x[1]**2;need(den!=0,'zero inverse');return (x[0]/den,-x[1]/den)
def div(x,y):return mul(x,inv(y))
def sq(x):return mul(x,x)
def pos(x):
 a,b=x
 if b==0:return a>0
 if a==0:return b>0
 if (a>0)==(b>0):return a>0
 return a*a>85*b*b if a>0 else 85*b*b>a*a
def total(xs):
 r=q(0)
 for x in xs:r=add(r,x)
 return r
def packed(x):return [str(v) for v in x]
alpha=[1,6,4,1]

def actual(u,d,mutation=False):
 nodes=list(product(range(4),repeat=d));origin=(0,)*d
 def value(x,l):
  z=u[x[0]] if l==1 else q(0)
  return add(z,q(1)) if mutation and x==origin and l==1 else z
 def shift(x,i,k):
  z=list(x);z[i]=(z[i]+k)%4;return tuple(z)
 norm=total(sq(value(x,l)) for x in nodes for l in range(d))
 energy=total(scale(sq(sub(value(shift(x,i,1),l),value(x,l))),alpha[x[0]]) for x in nodes for i in range(d) for l in range(d))
 divergence=[total(sub(value(x,l),value(shift(x,l,-1),l)) for l in range(d)) for x in nodes]
 observation=q(0)
 for y in product(range(4),repeat=d-1):
  for interval in ((0,1),(2,3)):
   for l in range(d):observation=add(observation,scale(sq(total(value((t,)+y,l) for t in interval)),F(1,2)))
 return norm,energy,observation,divergence

def cases(out):
 out.mkdir(exist_ok=False);rows=[];s=(F(0),F(1));cs=scale(sub(q(17),s),F(1,2));v=[q(7),q(-7),sub(q(6),s),sub(s,q(6))]
 for d in (3,4):
  factor=4**(d-1);u=[q(F(x,14)) for x in (19,-9,-5,-5)]
  norm,energy,obs,dg=actual(u,d);need(all(x==q(0) for x in dg),'actual fixed divergence')
  need(norm==q(F(123,49)*factor) and energy==q(F(52,7)*factor) and obs==q(F(25,49)*factor),'actual fixed normalization')
  defect=add(energy,scale(sub(obs,norm),F(19,5)));need(defect==q(-F(6,35)*factor),'actual fixed negative defect')
  rows.append({'D':d,'kind':'fixed19/5','norm':packed(norm),'energy':packed(energy),'observation_norm':packed(obs),'defect':packed(defect),'divergence_nonzero':0})
  for K in (0,1,100):
   den=sub(q(7+K),cs);b=sub(q(13),s);need(pos(den) and pos(b),'positive algebraic denominator')
   delta=div(scale(b,5),den);pp=[scale(delta,F(t,2)) for t in (1,1,-1,-1)];u=[add(x,y) for x,y in zip(v,pp)]
   norm,energy,obs,dg=actual(u,d);need(all(x==q(0) for x in dg),'actual equality divergence')
   defect=sub(add(energy,scale(obs,K)),mul(cs,norm));expected=scale(div(scale(sq(b),-25),den),factor)
   need(defect==expected and pos(neg(defect)),'actual equality negative defect')
   rows.append({'D':d,'kind':'endpoint','K':K,'delta':packed(delta),'norm':packed(norm),'energy':packed(energy),'observation_norm':packed(obs),'defect':packed(defect),'divergence_nonzero':0})
  _,_,_,bad=actual([q(F(x,14)) for x in (19,-9,-5,-5)],d,mutation=True)
  need(sum(z!=q(0) for z in bad)==2,'changed actual field divergence guard')
 need(len(rows)==8,'actual case count')
 result={'status':'FINITE_ACTUAL_PHYSICAL_DIAGNOSTICS_PASS','cases':rows,'actual_cases_checked':8,'mutated_fields_detected':2,'scope':'D3/4,n4 only; full analytic lift proof is separate; no Lean or independent reproduction'}
 (out/'result.json').write_text(json.dumps(result,sort_keys=True,indent=2));print(json.dumps(result),flush=True)

def main(root):
 root.mkdir(exist_ok=False);report={'status':'RUNNING','steps':[],'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'assert_nodes':None}
 try:
  import ast
  need(not any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(Path(__file__).read_text()))),'assert-dependent acceptance');report['assert_nodes']=0
  for mode,flags in [('normal',[]),('optimized',['-O'])]:
   t=time.monotonic();r=subprocess.run([sys.executable]+flags+[__file__,'--cases',str(root/mode)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=300,env=dict(os.environ,PYTHONHASHSEED='0'))
   (root/(mode+'.log')).write_text(r.stdout);tmp=root/(mode+'.exit.tmp');tmp.write_text(str(r.returncode)+'\n');need(re.fullmatch(r'-?\d+\n',tmp.read_text()) is not None,'sentinel');tmp.replace(root/(mode+'.exit.txt'))
   report['steps'].append({'mode':mode,'exit':r.returncode,'seconds':time.monotonic()-t});need(r.returncode==0,mode+' failed')
  normal=(root/'normal/result.json').read_bytes();need(normal==(root/'optimized/result.json').read_bytes(),'mode mismatch')
  report.update(status='FINITE_ACTUAL_PHYSICAL_DIAGNOSTICS_PASS',summary=json.loads(normal),matching_bytes=True)
 except Exception as e:report.update(status='FAILED',error=str(e),traceback=traceback.format_exc())
 finally:
  (root/'diagnose142.py').write_bytes(Path(__file__).read_bytes());(root/'report.json').write_text(json.dumps(report,indent=2))
  (root/'SHA256.json').write_text(json.dumps({str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in root.rglob('*') if f.is_file()},indent=2))
  zpath=root.with_suffix('.zip')
  with zipfile.ZipFile(zpath,'w',zipfile.ZIP_DEFLATED) as z:
   for f in sorted(root.rglob('*')):
    if f.is_file():z.write(f,str(f.relative_to(root)))
  print(json.dumps({'status':report['status'],'zip_sha256':hashlib.sha256(zpath.read_bytes()).hexdigest(),'zip_bytes':zpath.stat().st_size}),flush=True)
  if report['status']=='FAILED':raise SystemExit(1)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--cases');p.add_argument('--out');a=p.parse_args()
 if a.cases:cases(Path(a.cases))
 else:main(Path(a.out))
