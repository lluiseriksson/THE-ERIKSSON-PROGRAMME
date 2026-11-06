import base64,hashlib,json,pathlib,platform,subprocess,sys,time,urllib.request,zipfile,datetime
start=time.monotonic()
out=pathlib.Path('/content/tep-unit151');out.mkdir(exist_ok=True)
source='564b84230478cb8d40505cb67985470e9bae699d'
expected={'verify151.py':'11eeb5de6386dcf5d73a74eef42c4c1ba87563c9214a2701ba34cc802f475344','energy-and-threshold-proof.txt':'04cd2660822ca290f31bce6f24791bf1912482f72b08f4ce267855f1ea064260'}
report={'unit':151,'source_sha':source,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':sys.version,'platform':platform.platform(),'status':'RUNNING','steps':[],'Lean_verified':False,'paired_reproduction':False}
try:
 for name,digest in expected.items():
  data=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+source+'/papers/flat-coarse-rank/energy-closure151/'+name,timeout=40).read()
  if hashlib.sha256(data).hexdigest()!=digest:raise ValueError('source hash mismatch '+name)
  (out/name).write_bytes(data)
 outputs=[]
 for label,flags in [('normal',[]),('optimized',['-O'])]:
  t=time.monotonic();p=subprocess.run([sys.executable,*flags,str(out/'verify151.py')],capture_output=True,text=True,timeout=30)
  (out/(label+'.stdout.txt')).write_text(p.stdout);(out/(label+'.stderr.txt')).write_text(p.stderr);(out/(label+'.exit.txt')).write_text(str(p.returncode)+'\n')
  report['steps'].append({'mode':label,'seconds':time.monotonic()-t,'exit':p.returncode})
  if p.returncode!=0:raise ValueError('actual checker failed '+label)
  obj=json.loads(p.stdout)
  if obj['accepted']!=5 or obj['real_mutations_rejected']!=3:raise ValueError('actual counters differ')
  outputs.append(p.stdout)
 if outputs[0]!=outputs[1]:raise ValueError('normal/optimized outputs differ')
 report['status']='EXACT_IDENTITY_NORMAL_OPTIMIZED_PASS';report['checker_result']=json.loads(outputs[0]);report['outputs_match']=True
except Exception as e:
 report['status']='FAILED';report['error']=repr(e)
finally:
 report['driver_seconds']=time.monotonic()-start;report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 (out/'run-report.json').write_text(json.dumps(report,indent=2,sort_keys=True))
 manifest={p.name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in out.iterdir() if p.is_file() and p.name!='SHA256.json'}
 (out/'SHA256.json').write_text(json.dumps(manifest,indent=2,sort_keys=True))
 z=pathlib.Path('/content/tep-unit151.zip')
 with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as archive:
  for p in sorted(out.iterdir()):
   if p.is_file():archive.write(p,p.name)
 b=z.read_bytes();print('REPORT151 '+json.dumps(report,sort_keys=True));print('META151 '+json.dumps({'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}));print('ZIP151 '+base64.b64encode(b).decode())
