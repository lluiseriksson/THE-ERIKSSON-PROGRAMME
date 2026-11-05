# Execute only in this chat's own Colab CPU/high-RAM Linux runtime.
import argparse,ast,hashlib,json,pathlib,platform,re,subprocess,sys,time,traceback,urllib.request,zipfile,os
from datetime import datetime,timezone
p=argparse.ArgumentParser();p.add_argument('--source-sha',required=True);a=p.parse_args()
ROOT=pathlib.Path('/content/tep-cube-fixtures139');ROOT.mkdir(exist_ok=False)
report={'unit':139,'source_sha':a.source_sha,'started_utc':datetime.now(timezone.utc).isoformat(),'steps':[],
        'status':'RUNNING','python':sys.version,'platform':platform.platform(),'scope':'Finite exact certificates only; no Lean, universal proof certificate or physical gap'}
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
try:
 url='https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+a.source_sha+'/reproducibility/explicit-cube-partition-20261105/cube_partition_fixtures.py'
 data=urllib.request.urlopen(url,timeout=60).read().replace(b'\r\n',b'\n')
 if hashlib.sha256(data).hexdigest()!='19bf98ba04ff6221a59baeb7cdefcfcf93f3e5dd956a855dc453eddb68ff5331':raise ValueError('Fixture script hash')
 source=ROOT/'cube_partition_fixtures.py';source.write_bytes(data)
 if any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(data))):raise ValueError('Acceptance-safe source must contain no assert')
 report['assert_nodes']=0
 for mode,flags in [('normal',[]),('optimized',['-O'])]:
  start=time.monotonic();r=subprocess.run([sys.executable]+flags+[str(source),'--out',str(ROOT/mode)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=300,env=dict(os.environ,PYTHONHASHSEED='0'))
  (ROOT/(mode+'.log')).write_text(r.stdout)
  temp=ROOT/(mode+'.exit.tmp');temp.write_text(str(r.returncode)+'\n')
  code=temp.read_text()
  if not re.fullmatch(r'-?\d+\n',code) or int(code)!=r.returncode:raise ValueError('Exit sentinel serialization')
  temp.replace(ROOT/(mode+'.exit.txt'))
  report['steps'].append({'mode':mode,'exit_code':r.returncode,'seconds':time.monotonic()-start})
  if r.returncode:raise RuntimeError(mode+' failed: '+r.stdout[-2200:])
  value=json.loads((ROOT/mode/'result.json').read_text())
  if value.get('status')!='FIXTURES_PASS' or value.get('certificates_accepted')!=8 or value.get('actual_mutations_rejected')!=value.get('actual_mutations_tested') or value.get('actual_mutations_rejected',0)<=0 or value.get('bad_inputs_rejected')!=2:raise ValueError('Actual fixture counters')
 files1={str(f.relative_to(ROOT/'normal')):sha(f) for f in sorted((ROOT/'normal').glob('*.json'))}
 files2={str(f.relative_to(ROOT/'optimized')):sha(f) for f in sorted((ROOT/'optimized').glob('*.json'))}
 if not files1 or files1!=files2:raise ValueError('Normal/optimized certificate bytes differ')
 report.update(status='FINITE_EXACT_FIXTURES_PASS',matching_json_files=len(files1),canonical_result_sha256=sha(ROOT/'normal'/'result.json'),summary=json.loads((ROOT/'normal'/'result.json').read_text()))
except Exception as e:
 report.update(status='FAILED',error=str(e),traceback=traceback.format_exc())
finally:
 report['finished_utc']=datetime.now(timezone.utc).isoformat()
 (ROOT/'run-report.json').write_text(json.dumps(report,indent=2))
 (ROOT/'run139.py').write_bytes(pathlib.Path(__file__).read_bytes())
 manifest={str(f.relative_to(ROOT)):sha(f) for f in sorted(ROOT.rglob('*')) if f.is_file()}
 (ROOT/'SHA256.json').write_text(json.dumps(manifest,indent=2))
 package=pathlib.Path('/content/tep-cube-fixtures139.zip')
 with zipfile.ZipFile(package,'w',zipfile.ZIP_DEFLATED) as z:
  for f in sorted(ROOT.rglob('*')):
   if f.is_file():z.write(f,str(f.relative_to(ROOT)))
 print(json.dumps({'report':report,'zip_sha256':sha(package),'zip_bytes':package.stat().st_size}),flush=True)
 if report['status']=='FAILED':raise SystemExit(1)
