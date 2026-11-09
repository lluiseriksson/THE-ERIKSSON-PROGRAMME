import os,sys,time,json,hashlib,subprocess,resource,zipfile,urllib.request,traceback
from pathlib import Path
from datetime import datetime,timezone
if not Path('/content').is_dir():raise RuntimeError('Owned Colab Linux only')
SOURCE='c993dff04868d01d37b6ec87e0417da3c91a1330'
PINS={'papers/flat-coarse-rank/research/2026-11-09_balanced-ring222.txt':'f2cd7941ccc8e9fa30e3a8742d5e814b0e4bcdc83ded16426b48b78c7deac057','scripts/balanced_ring_diagnostic222.py':'f87e76462f346037e10e16ff9713f2a15ddb46337f997955bb18fbf188cf0dd5'}
out=Path('/content/tep222');out.mkdir(exist_ok=False)
start=time.monotonic();report={'source_sha':SOURCE,'input_pins':PINS,'started_utc':datetime.now(timezone.utc).isoformat(),'billed_units':None,'exits':{}}
try:
 for name,digest in PINS.items():
  raw=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/'+name,timeout=45).read()
  if hashlib.sha256(raw).hexdigest()!=digest:raise RuntimeError('Pinned raw Git bytes differ')
  (out/Path(name).name).write_bytes(raw)
 for mode,flags in [('normal',[]),('optimized',['-O'])]:
  p=subprocess.run([sys.executable,*flags,str(out/'balanced_ring_diagnostic222.py')],capture_output=True,timeout=360)
  (out/(mode+'.stdout.json')).write_bytes(p.stdout);(out/(mode+'.stderr.txt')).write_bytes(p.stderr)
  tmp=out/(mode+'.exit.tmp');tmp.write_text(str(p.returncode)+'\n');code=int(tmp.read_text().strip());os.replace(tmp,out/(mode+'.exit'));report['exits'][mode]=code
  if code:raise RuntimeError(mode+' failed, exact failure retained')
  v=json.loads(p.stdout)
  if v['status']!='FINITE_RATIONAL_DIAGNOSTICS_CHECKED' or v['partitions']!=200 or v['global_fields']!=800 or v['negative_controls_rejected']!=3:raise RuntimeError('Acceptance counters differ')
 if (out/'normal.stdout.json').read_bytes()!=(out/'optimized.stdout.json').read_bytes():raise RuntimeError('Mode mismatch')
 report['status']='FINITE_DIAGNOSTICS_CHECKED'
except Exception:
 report['status']='FAILED_PRESERVED';(out/'failure.txt').write_text(traceback.format_exc())
finally:
 report.update(finished_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-start,child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
 (out/'report222.json').write_text(json.dumps(report,indent=2)+'\n')
 manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file()};(out/'manifest222.json').write_text(json.dumps(manifest,indent=2)+'\n')
 with zipfile.ZipFile('/content/tep222-diagnostic.zip','w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(out.iterdir()):
   if p.is_file():z.write(p,p.name)
 print(json.dumps(report))
if report['status']!='FINITE_DIAGNOSTICS_CHECKED':raise RuntimeError('Preserved failed diagnostic run')
