import os,sys,time,json,hashlib,subprocess,resource,zipfile,urllib.request,traceback
from pathlib import Path
from datetime import datetime,timezone
if not Path('/content').is_dir():raise RuntimeError('Owned Colab only')
SOURCE='0c79cd67a002c24a305b70cf707c420aa1bd9ae3'
PINS={'papers/flat-coarse-rank/research/2026-11-09_offcenter-shell220.txt': '286577395ab9d13e2e75a010d764c9d926b0dd6601e8b1afef6599b8885578c3', 'scripts/offcenter_shell_diagnostic220.py': 'ec80c950ea2457f706c054989000379e1f326b5efb7fc96b389736b4c9a0aee0'}
out=Path('/content/tep220');out.mkdir(exist_ok=False)
start=time.monotonic();report={'source_sha':SOURCE,'started_utc':datetime.now(timezone.utc).isoformat(),'billed_units':None,'exits':{}}
try:
 for name,digest in PINS.items():
  raw=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/'+name,timeout=45).read()
  if hashlib.sha256(raw).hexdigest()!=digest:raise RuntimeError('Pinned bytes mismatch')
  (out/Path(name).name).write_bytes(raw)
 for mode,flags in [('normal',[]),('optimized',['-O'])]:
  p=subprocess.run([sys.executable,*flags,str(out/'offcenter_shell_diagnostic220.py')],capture_output=True,timeout=180)
  (out/(mode+'.stdout.json')).write_bytes(p.stdout);(out/(mode+'.stderr.txt')).write_bytes(p.stderr)
  tmp=out/(mode+'.exit.tmp');tmp.write_text(str(p.returncode)+'\n');code=int(tmp.read_text().strip());os.replace(tmp,out/(mode+'.exit'));report['exits'][mode]=code
  if code:raise RuntimeError(mode+' failed')
  v=json.loads(p.stdout)
  if v['status']!='FINITE_RATIONAL_DIAGNOSTICS_CHECKED' or v['fields']!=20 or v['transport_checks']!=200 or v['negative_controls_rejected']!=3:raise RuntimeError('Acceptance mismatch')
 if (out/'normal.stdout.json').read_bytes()!=(out/'optimized.stdout.json').read_bytes():raise RuntimeError('Mode mismatch')
 report['status']='FINITE_DIAGNOSTICS_CHECKED'
except Exception:
 report['status']='FAILED_PRESERVED';(out/'failure.txt').write_text(traceback.format_exc())
finally:
 report.update(finished_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-start,child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
 (out/'report220.json').write_text(json.dumps(report,indent=2)+'\n')
 manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file()};(out/'manifest220.json').write_text(json.dumps(manifest,indent=2)+'\n')
 with zipfile.ZipFile('/content/tep220-diagnostic.zip','w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(out.iterdir()):
   if p.is_file():z.write(p,p.name)
 print(json.dumps(report))
if report['status']!='FINITE_DIAGNOSTICS_CHECKED':raise RuntimeError('Retained failure')
