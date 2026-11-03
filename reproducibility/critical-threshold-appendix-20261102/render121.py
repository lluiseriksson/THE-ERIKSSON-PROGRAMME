import os,sys,json,time,pathlib,subprocess,hashlib,urllib.request,zipfile,base64,traceback,re
from datetime import datetime,timezone
SOURCE='ba44a9f9e3d7ec976e082c4c863fdbe50282843e'
TEX_HASH='56460bffb7abaf16187bd07e168fc248bd15fe7a21d211da2dff371cccfc08ca'
MAP_HASH='1268e1bcaf0be45ae44bf9df83387dc9d5e453f6f07805c0534a784088b51e45'
ROOT=pathlib.Path('/content/tep-critical-appendix121');ROOT.mkdir(exist_ok=False)
OUT=ROOT/'evidence';OUT.mkdir();PUB=ROOT/'public-package';PUB.mkdir()
report={'run':'121','started_utc':datetime.now(timezone.utc).isoformat(),'source_sha':SOURCE,
 'status':'RUNNING','steps':[],'new_lean_run':False,'independent_review':False,
 'artifact_marker':'Official bundled marker executed exactly once on host immediately before TeX authoring'}

def digest(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def fetch(sha,path):
 return urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+sha+'/'+path,timeout=60).read()
def run(name,args):
 t=time.monotonic()
 p=subprocess.run(args,cwd=OUT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=600,
  env=dict(os.environ,DEBIAN_FRONTEND='noninteractive',SOURCE_DATE_EPOCH='1793577600',FORCE_SOURCE_DATE='1',TZ='UTC'))
 (OUT/(name+'.stdout.log')).write_text(p.stdout)
 tmp=OUT/(name+'.exit.tmp');tmp.write_text(str(p.returncode)+'\n')
 if tmp.read_text()!=str(p.returncode)+'\n':raise RuntimeError('Actual exit sentinel mismatch')
 tmp.replace(OUT/(name+'.exit.txt'))
 row={'name':name,'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3)}
 report['steps'].append(row);print(json.dumps(row),flush=True)
 if p.returncode:raise RuntimeError(name+' failed: '+p.stdout[-3000:])
 return p.stdout

try:
 tex=fetch(SOURCE,'papers/flat-coarse-rank/research-consolidation/critical-inverse-moment-appendix.tex').replace(b'\r\n',b'\n')
 mapping=fetch(SOURCE,'papers/flat-coarse-rank/research-consolidation/critical-inverse-moment-map.json').replace(b'\r\n',b'\n')
 if hashlib.sha256(tex).hexdigest()!=TEX_HASH:raise ValueError('TeX hash mismatch')
 if hashlib.sha256(mapping).hexdigest()!=MAP_HASH:raise ValueError('Map hash mismatch')
 (OUT/'critical-inverse-moment-appendix.tex').write_bytes(tex)
 (OUT/'provenance-map.json').write_bytes(mapping);m=json.loads(mapping)
 if m['private_access_state_included'] or m['new_lean_execution'] or m['independent_review']:raise ValueError('Scope flags')
 if m['public_code_revision']!='d40ac5934919eeca7e9b71c16cf055382ef1e032' or len(m['allowlist'])!=28:raise ValueError('Wrong public pin or count')
 rows=[]
 for path,want in m['allowlist'].items():
  rel=pathlib.PurePosixPath(path)
  if rel.is_absolute() or '..' in rel.parts or not path.startswith(('reproducibility/','YangMills/')):raise ValueError('Unsafe path')
  if rel.suffix not in {'.md','.py','.json','.ipynb','.zip','.lean'}:raise ValueError('Wrong type')
  data=fetch(m['public_code_revision'],path)
  if rel.suffix!='.zip':data=data.replace(b'\r\n',b'\n')
  if hashlib.sha256(data).hexdigest()!=want:raise ValueError('Public source mismatch '+path)
  target=PUB/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
  rows.append({'path':path,'sha256':want})
 (OUT/'allowlist-fetch.json').write_text(json.dumps(rows,indent=2))
 archived=PUB/'reproducibility/critical-fourier-fixtures-20261102/109-full-evidence.zip'
 with zipfile.ZipFile(archived) as z:
  manifest=json.loads(z.read('manifest.json'))
  for path,want in manifest.items():
   if hashlib.sha256(z.read(path)).hexdigest()!=want:raise ValueError('109 inner hash mismatch')
  if len(manifest)!=8:raise ValueError('109 inner count')
 inner_counts={'109':8}
 for rel,key,count in [('reproducibility/spatial-observation-audit-20261103/115-full-evidence.zip','115',73),('reproducibility/mean-penalty-cycle-lean-20261103/evidence/colab116-full.zip','116',34),('reproducibility/mean-penalty-cycle-lean-20261103/evidence/colab117-full.zip','117',34),('reproducibility/mean-penalty-cycle-lean-20261103/evidence/colab118-full.zip','118',69)]:
  with zipfile.ZipFile(PUB/rel) as z:
   im=json.loads(z.read('manifest.json'))
   if len(im)!=count:raise ValueError('Inner manifest count '+key)
   for path,want in im.items():
    if hashlib.sha256(z.read(path)).hexdigest()!=want:raise ValueError('Inner hash '+key+' '+path)
   inner_counts[key]=count
 report['allowlist_count']=28;report['diagnostic_inner_hashes_rechecked']=inner_counts
 run('apt-update',['apt-get','update','-qq'])
 run('apt-install',['apt-get','install','-y','-qq','texlive-latex-recommended','texlive-fonts-recommended','lmodern','poppler-utils'])
 run('pdflatex-pass1',['pdflatex','-interaction=nonstopmode','-halt-on-error','critical-inverse-moment-appendix.tex'])
 run('pdflatex-pass2',['pdflatex','-interaction=nonstopmode','-halt-on-error','critical-inverse-moment-appendix.tex'])
 info=run('pdfinfo',['pdfinfo','critical-inverse-moment-appendix.pdf'])
 run('pdftotext',['pdftotext','-layout','critical-inverse-moment-appendix.pdf','appendix.txt'])
 run('pdftoppm',['pdftoppm','-r','110','-png','critical-inverse-moment-appendix.pdf','page'])
 pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1])
 if not 5<=pages<=24 or len(list(OUT.glob('page-*.png')))!=pages:raise ValueError('Page count')
 log=(OUT/'critical-inverse-moment-appendix.log').read_text(errors='replace')
 warnings=[x for x in log.splitlines() if 'Overfull' in x or 'Underfull' in x or 'LaTeX Warning' in x]
 if any('Overfull' in x or 'undefined' in x.lower() for x in warnings):raise ValueError('Layout/reference warnings '+repr(warnings))
 txt=' '.join((OUT/'appendix.txt').read_text().split())
 anchors=['Actual objects and the original observation problem','The critical global moment theorem',
 'Every lower positive inverse exponent is insufficient','Model assessments and review context',
 'The single remaining bounded question','What a spatial observation proof must still establish']
 if not all(a in txt for a in anchors):raise ValueError('Missing text anchor')
 for name in ['critical-inverse-moment-appendix.tex','critical-inverse-moment-appendix.pdf','provenance-map.json']:
  (PUB/name).write_bytes((OUT/name).read_bytes())
 (PUB/'render121.py').write_bytes(pathlib.Path(__file__).read_bytes())
 (PUB/'REPRODUCE.txt').write_text('Existing-dossier appendix; no deposit. Source '+SOURCE+'.\nRun render121.py only in own authorized Colab Linux; exact pins/allowlist and all raw reports retained.\nThis assembly performs no new Lean or mathematical fixture run. Existing109/115 finite and118 focal Lean evidence plus116/117 failures are rehashed; no new theorem execution.\nThe first exact-PDF assessment is an external SHA-linked sidecar created AFTER visual review; this archive does not contain that later report. No source/PDF score inheritance or independent review.\n')
 manifest={str(p.relative_to(PUB)):digest(p) for p in sorted(PUB.rglob('*')) if p.is_file()}
 (PUB/'sha256-manifest.json').write_text(json.dumps(manifest,indent=2))
 package=OUT/'public-reproducibility.zip'
 with zipfile.ZipFile(package,'w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(PUB.rglob('*')):
   if p.is_file():z.write(p,str(p.relative_to(PUB)))
 report.update(status='PDF_RENDERED_AWAITING_FIRST_VISUAL_REVIEW',pages=pages,
  pdf_sha256=digest(OUT/'critical-inverse-moment-appendix.pdf'),tex_sha256=TEX_HASH,map_sha256=MAP_HASH,
  driver_sha256=digest(__file__),layout_warnings=warnings,public_package_entries=len(manifest)+1,
  public_package_sha256=digest(package))
 (OUT/'tool-versions.txt').write_text(subprocess.getoutput('pdflatex --version')+'\n'+subprocess.getoutput('pdftoppm -v'))
 (OUT/'package-versions.txt').write_text(subprocess.getoutput('dpkg-query -W texlive-latex-recommended texlive-fonts-recommended lmodern poppler-utils'))
except BaseException as e:
 report['status']='FAIL';report['error']=repr(e)
 (OUT/'exception.txt').write_text(traceback.format_exc());print(traceback.format_exc(),flush=True)
finally:
 report['finished_utc']=datetime.now(timezone.utc).isoformat();report['colab_gpu_env']=os.environ.get('COLAB_GPU','unset')
 (OUT/'report.json').write_text(json.dumps(report,indent=2))
 (OUT/'recipe121.py').write_bytes(pathlib.Path(__file__).read_bytes())
 manifest={p.name:digest(p) for p in sorted(OUT.iterdir()) if p.is_file()}
 (OUT/'manifest.json').write_text(json.dumps(manifest,indent=2))
 bundle=ROOT/'render121.zip'
 with zipfile.ZipFile(bundle,'w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(OUT.iterdir()):
   if p.is_file():z.write(p,p.name)
 print('FINAL_REPORT='+json.dumps(report),flush=True)
 print('BUNDLE_SHA256='+digest(bundle),flush=True)
 encoded=base64.b64encode(bundle.read_bytes()).decode()
 for k in range(0,len(encoded),16000):print('ZIPCHUNK:'+str(k//16000)+':'+encoded[k:k+16000],flush=True)
 print('ZIPCHUNKS_END',flush=True)
 print('PDF_ASSEMBLY_ONLY; releasing own runtime.',flush=True)
 from google.colab import runtime
 runtime.unassign()
