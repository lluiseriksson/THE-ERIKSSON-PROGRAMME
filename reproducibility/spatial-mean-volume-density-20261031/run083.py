import os,sys,time,json,pathlib,hashlib,subprocess,urllib.request,traceback,zipfile,base64
from datetime import datetime,timezone
SHA='e6b603252e63ee7ebfa2c5507023ad49acdd40c8'
EXPECTED={"pre-execution-objections.md":"ce0556d47628127734f4c6991833b1736eea5ae76f7e4d8201be27b801eb818f","check_packet.py":"76e874b2498592cf11d10774d03dc6b5454aa736724f816986a543821b9be6d6","proof.md":"addefc5b7e867402f945d39b9358f48e52e89e269cce34346ccc81d33deaba99"}
root=pathlib.Path('/content/eriksson-mean-density083');root.mkdir(exist_ok=True)
report={'source_sha':SHA,'started_utc':datetime.now(timezone.utc).isoformat(),'status':'PENDING','formal_verification':False,'independent_review':False,'steps':[]}
def digest(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
try:
 for name,h in EXPECTED.items():
  data=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SHA+'/reproducibility/spatial-mean-volume-density-20261031/'+name).read()
  if hashlib.sha256(data).hexdigest()!=h:raise RuntimeError('Source hash mismatch '+name)
  (root/name).write_bytes(data)
 for mode,flags in [('normal',[]),('optimized',['-O'])]:
  t=time.monotonic();p=subprocess.run([sys.executable,*flags,str(root/'check_packet.py')],capture_output=True,text=True,env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1'))
  (root/(mode+'.log')).write_text(p.stdout+p.stderr)
  report['steps'].append({'mode':mode,'exit_code':p.returncode,'seconds':time.monotonic()-t})
  if p.returncode:raise RuntimeError(mode+' failed: '+p.stderr[-3000:])
  value=json.loads(p.stdout)
  if value['status']!='FINITE_PROBES_PASS_NOT_A_PROOF' or len(value['cases'])!=7:raise RuntimeError('Incomplete probes')
  if value['optimized']!=(mode=='optimized'):raise RuntimeError('Mode mismatch')
  (root/(mode+'.json')).write_text(json.dumps(value,indent=2))
 normal=json.loads((root/'normal.json').read_text());optimized=json.loads((root/'optimized.json').read_text())
 if normal['cases']!=optimized['cases']:raise RuntimeError('Normal/optimized probe mismatch')
 report.update(status='FINITE_PROBES_AND_MUTATIONS_MATCH_NOT_A_UNIVERSAL_PROOF',cases=7,mutations_per_case=3,source_hashes=EXPECTED,normal_optimized_match=True)
except Exception:
 report['status']='FAILED';(root/'exception.txt').write_text(traceback.format_exc())
finally:
 report['finished_utc']=datetime.now(timezone.utc).isoformat()
 (root/'report.json').write_text(json.dumps(report,indent=2))
 files=sorted(p for p in root.iterdir() if p.is_file())
 (root/'manifest.json').write_text(json.dumps({p.name:digest(p) for p in files},indent=2))
 z=pathlib.Path('/content/mean-density083.zip')
 with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as archive:
  for p in sorted(root.iterdir()):
   if p.is_file():archive.write(p,p.name)
 print('FINAL_REPORT='+json.dumps(report),flush=True)
 print('BUNDLE_SHA256='+digest(z),flush=True)
 print('EVIDENCE_BASE64_BEGIN='+base64.b64encode(z.read_bytes()).decode()+'=EVIDENCE_BASE64_END',flush=True)
 from google.colab import runtime
 runtime.unassign()
