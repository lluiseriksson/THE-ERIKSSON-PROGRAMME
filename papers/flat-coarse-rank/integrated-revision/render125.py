import os,json,time,pathlib,subprocess,hashlib,urllib.request,zipfile,base64,traceback,re,io
from datetime import datetime,timezone
SOURCE='d199a0977eca581b2e0d00c1afd84233a8db361d'
INPUTS={"main-declaration-map.json":"2ec3658252c36ea9ea3b60fca4a0004147782499452814653952d7ae2932aa61","flat_critical_integrated.tex":"97dcbdb96e4dcc2f8eb3c892ea164c0dfdb4b887abd62f6e70a2a4bcf8fef621","critical-declaration-map.json":"6b4632fa8b44559b56285ff8196eb97f7d5df64bd38433f1301ff55bde9397b9","integration-map.json":"4c0f4c347a247b7751aea00c1957cfb3ff037ad2d6004670f5ccf4da08324095"}
ROOT=pathlib.Path('/content/tep-integrated125');ROOT.mkdir(exist_ok=False)
OUT=ROOT/'evidence';OUT.mkdir();PUB=ROOT/'public';PUB.mkdir()
report={'run':'125','source_sha':SOURCE,'started_utc':datetime.now(timezone.utc).isoformat(),
 'steps':[],'status':'RUNNING','new_lean_execution':False,'new_numerical_execution':False,
 'independent_review':False,'old_scores_inherited':False,
 'artifact_marker':'Official bundled marker once on host before integrated TeX authoring'}
def digest(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def fetch(sha,p):return urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+sha+'/'+p,timeout=90).read()
def run(name,args):
 t=time.monotonic();p=subprocess.run(args,cwd=OUT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=600,
  env=dict(os.environ,DEBIAN_FRONTEND='noninteractive',SOURCE_DATE_EPOCH='1793775722',FORCE_SOURCE_DATE='1',TZ='UTC'))
 (OUT/(name+'.log')).write_text(p.stdout);(OUT/(name+'.exit.txt')).write_text(str(p.returncode)+'\n')
 row={'name':name,'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3)}
 report['steps'].append(row);print(json.dumps(row),flush=True)
 if p.returncode:raise RuntimeError(name+' failed '+p.stdout[-2400:])
 return p.stdout
try:
 for name,want in INPUTS.items():
  data=fetch(SOURCE,'papers/flat-coarse-rank/integrated-revision/'+name).replace(b'\r\n',b'\n')
  if hashlib.sha256(data).hexdigest()!=want:raise ValueError('Input hash '+name)
  (OUT/name).write_bytes(data);(PUB/name).write_bytes(data)
 old=fetch('a8091f9a64879351b938415c648b670324fcb535','reproducibility/critical-threshold-appendix-20261102/122-public-reproducibility.zip')
 if hashlib.sha256(old).hexdigest()!='5051358a23b033dc9d97d01a1016ff081537ab546e6bc920e99604d9c612a997':raise ValueError('Prior evidence package')
 (PUB/'critical-prior-evidence122.zip').write_bytes(old)
 with zipfile.ZipFile(io.BytesIO(old)) as z:
  manifest=json.loads(z.read('sha256-manifest.json'))
  for name,want in manifest.items():
   if hashlib.sha256(z.read(name)).hexdigest()!=want:raise ValueError('Prior inner '+name)
  report['prior_package_files_rehashed']=len(manifest)
 tex=(OUT/'flat_critical_integrated.tex').read_text()
 labels=re.findall(r'\\label\{([^}]+)\}',tex)
 if len(labels)!=len(set(labels)):raise ValueError('Duplicate TeX labels')
 report['unique_labels']=len(labels)
 run('apt-update',['apt-get','update','-qq'])
 run('apt-install',['apt-get','install','-y','-qq','texlive-latex-recommended','texlive-fonts-recommended','lmodern','poppler-utils'])
 for k in (1,2):run('pdflatex-pass'+str(k),['pdflatex','-interaction=nonstopmode','-halt-on-error','flat_critical_integrated.tex'])
 info=run('pdfinfo',['pdfinfo','flat_critical_integrated.pdf'])
 run('pdftotext',['pdftotext','-layout','flat_critical_integrated.pdf','integrated.txt'])
 run('pdftoppm',['pdftoppm','-r','100','-png','flat_critical_integrated.pdf','page'])
 pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1])
 if not 25<=pages<=45 or len(list(OUT.glob('page-*.png')))!=pages:raise ValueError('Page count')
 warnings=[l for l in (OUT/'flat_critical_integrated.log').read_text(errors='replace').splitlines() if any(w in l for w in ['Overfull','Underfull','LaTeX Warning'])]
 if any('Overfull' in l or 'undefined' in l.lower() or 'multiply defined' in l.lower() for l in warnings):raise ValueError('Layout/reference '+repr(warnings))
 text=' '.join((OUT/'integrated.txt').read_text().split())
 for anchor in ['Coarse information and finite rank obstructions','From necessary rank budgets to sufficient observations','The critical global moment theorem','Constructive rectangular bounds and their limits','The exact cube decomposition is not universal','Model assessments and review context']:
  if anchor not in text:raise ValueError('Missing content '+anchor)
 (PUB/'flat_critical_integrated.pdf').write_bytes((OUT/'flat_critical_integrated.pdf').read_bytes())
 (PUB/'render125.py').write_bytes(pathlib.Path(__file__).read_bytes())
 (PUB/'REPRODUCE.txt').write_text('Single integrated manuscript, not a second deposit. Source '+SOURCE+'. Run render125.py only in own authorized Colab Linux. Exact TeX/maps and prior critical evidence package rehashed. Main declaration map references immutable earlier formal endpoints; their whole dependency closure is not rerun or repackaged here. No new Lean/oracle/numerical run. No historical license/grant or old review score inherited. First exact integrated-PDF review is a later hash-linked sidecar.\n')
 manifest={p.name:digest(p) for p in sorted(PUB.iterdir()) if p.is_file()}
 (PUB/'sha256-manifest.json').write_text(json.dumps(manifest,indent=2))
 package=OUT/'public-reproducibility.zip'
 with zipfile.ZipFile(package,'w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(PUB.iterdir()):z.write(p,p.name)
 report.update(status='INTEGRATED_PDF_AWAITING_FIRST_VISUAL_REVIEW',pages=pages,
  pdf_sha256=digest(OUT/'flat_critical_integrated.pdf'),pdf_bytes=(OUT/'flat_critical_integrated.pdf').stat().st_size,
  layout_warnings=warnings,public_package_sha256=digest(package),public_package_entries=len(manifest)+1,
  driver_sha256=digest(__file__),input_hashes=INPUTS)
 (OUT/'tool-versions.txt').write_text(subprocess.getoutput('pdflatex --version')+'\n'+subprocess.getoutput('pdftoppm -v'))
except BaseException as e:
 report.update(status='FAIL',error=repr(e));(OUT/'exception.txt').write_text(traceback.format_exc());print(traceback.format_exc(),flush=True)
finally:
 report['finished_utc']=datetime.now(timezone.utc).isoformat();report['colab_gpu_env']=os.environ.get('COLAB_GPU','unset')
 (OUT/'report.json').write_text(json.dumps(report,indent=2));(OUT/'recipe125.py').write_bytes(pathlib.Path(__file__).read_bytes())
 manifest={p.name:digest(p) for p in sorted(OUT.iterdir()) if p.is_file()}
 (OUT/'manifest.json').write_text(json.dumps(manifest,indent=2));bundle=ROOT/'render125.zip'
 with zipfile.ZipFile(bundle,'w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(OUT.iterdir()):
   if p.is_file():z.write(p,p.name)
 print('FINAL_REPORT='+json.dumps(report),flush=True);print('BUNDLE_SHA256='+digest(bundle),flush=True)
 encoded=base64.b64encode(bundle.read_bytes()).decode()
 for i in range(0,len(encoded),16000):print('ZIPCHUNK:'+str(i//16000)+':'+encoded[i:i+16000],flush=True)
 print('ZIPCHUNKS_END',flush=True);print('ASSEMBLY_ONLY; releasing own runtime',flush=True)
 from google.colab import runtime
 runtime.unassign()
