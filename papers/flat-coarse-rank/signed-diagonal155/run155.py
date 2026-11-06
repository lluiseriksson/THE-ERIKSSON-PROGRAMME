# Own Colab Linux only. No Lean or external dependencies; preserve real failures.
import argparse,urllib.request,pathlib,json,hashlib,subprocess,time,zipfile,traceback
from datetime import datetime,timezone
p=argparse.ArgumentParser();p.add_argument('--source-sha',required=True);a=p.parse_args()
R=pathlib.Path('/content/tep-signed155');R.mkdir(exist_ok=False)
r={'unit':155,'source_sha':a.source_sha,'started_utc':datetime.now(timezone.utc).isoformat(),'steps':[],'status':'RUNNING','Lean':False,'scope':'exact finite diagnostics; analytic proof not formal/independent review'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fetch(p):return urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+a.source_sha+'/'+p,timeout=60).read()
try:
 m=json.loads(fetch('papers/flat-coarse-rank/signed-diagonal155/inputs.json'));(R/'inputs.json').write_text(json.dumps(m,indent=2))
 for nm,it in m.items():
  b=fetch(it['path']).replace(b'\r\n',b'\n')
  if hashlib.sha256(b).hexdigest()!=it['sha256']:raise ValueError('input hash '+nm)
  (R/nm).write_bytes(b)
 for mode,flags in [('normal',[]),('optimized',['-O'])]:
  start=time.monotonic();ch=subprocess.run(['python3']+flags+['verify155.py','--out',mode+'.json'],cwd=R,capture_output=True,text=True,timeout=180)
  (R/(mode+'.log')).write_text(ch.stdout+'\nSTDERR\n'+ch.stderr);tmp=R/(mode+'.exit.tmp');tmp.write_text(str(ch.returncode)+'\n')
  if not tmp.read_text().strip() or int(tmp.read_text())!=ch.returncode:raise ValueError('sentinel')
  tmp.replace(R/(mode+'.exit.txt'));r['steps'].append({'mode':mode,'exit_code':ch.returncode,'seconds':time.monotonic()-start})
  if ch.returncode:raise ValueError(mode+' failed: '+ch.stderr[-1000:])
 if (R/'normal.json').read_bytes()!=(R/'optimized.json').read_bytes():raise ValueError('normal/optimized mathematics differs')
 result=json.loads((R/'normal.json').read_text())
 if result['accepted_identity_cases']!=6 or result['accepted_witness_records']!=48 or len(result['actual_mutations_rejected'])!=3:raise ValueError('bad diagnostic count')
 r.update(status='ONE_RUNTIME_EXACT_DIAGNOSTICS_PASS',mathematical_output_sha256=sha(R/'normal.json'),normal_optimized_identical=True,identities=6,witness_records=48,rejected_actual_mutations_per_mode=3,paired_fresh_clones=False)
except Exception as e:r.update(status='FAILED',error=str(e),traceback=traceback.format_exc())
finally:
 r['finished_utc']=datetime.now(timezone.utc).isoformat();(R/'run155.py').write_bytes(pathlib.Path(__file__).read_bytes());(R/'report.json').write_text(json.dumps(r,indent=2))
 (R/'SHA256.json').write_text(json.dumps({f.name:sha(f) for f in sorted(R.iterdir()) if f.is_file()},indent=2))
 z=pathlib.Path('/content/tep-signed155.zip')
 with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as q:
  for f in sorted(R.iterdir()):
   if f.is_file():q.write(f,f.name)
 print(json.dumps({'report':r,'zip_sha256':sha(z),'zip_bytes':z.stat().st_size}),flush=True)
 if r['status']=='FAILED':raise SystemExit(1)