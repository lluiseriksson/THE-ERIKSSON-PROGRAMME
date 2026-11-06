# Colab Linux only. Prepared offline; preserve all failures and recover before disconnect.
import argparse,pathlib,urllib.request,hashlib,json,subprocess,os,time,re,zipfile,traceback
from datetime import datetime,timezone
p=argparse.ArgumentParser();p.add_argument('--source-sha',required=True);a=p.parse_args()
ROOT=pathlib.Path('/content/tep-companion152');ROOT.mkdir(exist_ok=False)
report={'unit':152,'source_sha':a.source_sha,'started_utc':datetime.now(timezone.utc).isoformat(),'steps':[],'status':'RUNNING','fixtures_rerun':False,'lean_rerun':False,'skills':['pdf','documents writing guidance','access-coordinator artifact scope']}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fetch(path):return urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+a.source_sha+'/'+path,timeout=90).read()
def step(name,cmd):
 t=time.monotonic();r=subprocess.run(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=600,env=dict(os.environ,DEBIAN_FRONTEND='noninteractive',SOURCE_DATE_EPOCH='1793836800',FORCE_SOURCE_DATE='1',TZ='UTC'))
 (ROOT/(name+'.log')).write_text(r.stdout)
 tmp=ROOT/(name+'.exit.tmp');tmp.write_text(str(r.returncode)+'\n')
 if not re.fullmatch(r'-?\d+\n',tmp.read_text()):raise ValueError('sentinel serialization')
 tmp.replace(ROOT/(name+'.exit.txt'));report['steps'].append({'name':name,'exit_code':r.returncode,'seconds':time.monotonic()-t});print(json.dumps(report['steps'][-1]),flush=True)
 if r.returncode:raise RuntimeError(name+' failed: '+r.stdout[-2000:])
 return r.stdout
try:
 manifest=json.loads(fetch('papers/flat-coarse-rank/companion-revision152/inputs.json'));(ROOT/'inputs.json').write_text(json.dumps(manifest,indent=2))
 for name,item in manifest.items():
  data=fetch(item['path'])
  if not item['binary']:data=data.replace(b'\r\n',b'\n')
  if hashlib.sha256(data).hexdigest()!=item['sha256']:raise ValueError('Pinned input mismatch: '+name)
  (ROOT/name).write_bytes(data)
 for nm in ('full-form148-first-clone-evidence.zip','full-form148-second-clone-evidence.zip','tep-cube-fixtures139.zip'):
  with zipfile.ZipFile(ROOT/nm) as z:
   hm=json.loads(z.read('SHA256.json'))
   for fn,sh in hm.items():
    if hashlib.sha256(z.read(fn)).hexdigest()!=sh:raise ValueError('Inner evidence hash mismatch: '+nm+'/'+fn)
 for nm in ('exact-evidence151.zip',):
  with zipfile.ZipFile(ROOT/nm) as z:
   hm=json.loads(z.read('SHA256.json'))
   for fn,item in hm.items():
    if hashlib.sha256(z.read(fn)).hexdigest()!=item['sha256']:raise ValueError('Unit151 inner hash mismatch: '+fn)
 step('apt-update',['apt-get','update','-qq'])
 step('apt-install',['apt-get','install','-y','-qq','texlive-latex-recommended','texlive-fonts-recommended','lmodern','poppler-utils'])
 for k in (1,2,3):step('pdflatex-pass'+str(k),['pdflatex','-interaction=nonstopmode','-halt-on-error','companion.tex'])
 warnings=[s for s in (ROOT/'companion.log').read_text(errors='replace').splitlines() if any(v in s for v in ('Overfull','Underfull','LaTeX Warning'))];report['warnings']=warnings
 if warnings:raise ValueError('Layout/reference warnings; retain and repair')
 info=step('pdfinfo',['pdfinfo','companion.pdf']);pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1])
 step('pdftotext',['pdftotext','-layout','companion.pdf','paper.txt'])
 step('render-pages',['pdftoppm','-r','80','-jpeg','-jpegopt','quality=86','companion.pdf','page'])
 if not 10<=pages<=30 or len(list(ROOT.glob('page-*.jpg')))!=pages:raise ValueError('Page count mismatch')
 text=(ROOT/'paper.txt').read_text()
 for phrase in ('Model assessments and review context','0c706827dcbb11859e56bb6c7dc981eb37a02e69','paired','divergence'):
  if phrase not in text:raise ValueError('Required context absent: '+phrase)
 report.update(status='RENDERED_AWAITING_FULL_VISUAL_QA',pages=pages,pdf_sha256=digest(ROOT/'companion.pdf'))
except Exception as e:report.update(status='FAILED',error=str(e),traceback=traceback.format_exc())
finally:
 report['finished_utc']=datetime.now(timezone.utc).isoformat();(ROOT/'render152.py').write_bytes(pathlib.Path(__file__).read_bytes());(ROOT/'render-report.json').write_text(json.dumps(report,indent=2))
 (ROOT/'SHA256.json').write_text(json.dumps({str(f.relative_to(ROOT)):digest(f) for f in sorted(ROOT.rglob('*')) if f.is_file()},indent=2))
 zpath=pathlib.Path('/content/tep-companion152.zip')
 with zipfile.ZipFile(zpath,'w',zipfile.ZIP_DEFLATED) as z:
  for f in sorted(ROOT.rglob('*')):
   if f.is_file():z.write(f,str(f.relative_to(ROOT)))
 print(json.dumps({'report':report,'zip_sha256':digest(zpath),'zip_bytes':zpath.stat().st_size}),flush=True)
 if report['status']=='FAILED':raise SystemExit(1)
