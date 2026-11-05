# Run only in this chat's own Colab Linux runtime. No Lean/oracle execution.
import argparse, pathlib, urllib.request, hashlib, subprocess, os, json, time, re, zipfile, traceback
from datetime import datetime, timezone
p=argparse.ArgumentParser(); p.add_argument('--source-sha',required=True); args=p.parse_args()
ROOT=pathlib.Path('/content/tep-revision136'); ROOT.mkdir(exist_ok=False)
OUT=ROOT/'output'; OUT.mkdir(); REPORT={'unit':136,'source_sha':args.source_sha,'started_utc':datetime.now(timezone.utc).isoformat(),'steps':[],'status':'RUNNING','new_lean_execution':False,'new_numerical_execution':False,'prior_score_transferred':False}
def digest(f):return hashlib.sha256(pathlib.Path(f).read_bytes()).hexdigest()
def fetch(repo,sha,path):return urllib.request.urlopen('https://raw.githubusercontent.com/'+repo+'/'+sha+'/'+path,timeout=90).read().replace(b'\r\n',b'\n')
def run(name,cmd):
 t=time.monotonic(); v=subprocess.run(cmd,cwd=OUT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=600,env=dict(os.environ,DEBIAN_FRONTEND='noninteractive',SOURCE_DATE_EPOCH='1793856000',FORCE_SOURCE_DATE='1',TZ='UTC'))
 (OUT/(name+'.log')).write_text(v.stdout); (OUT/(name+'.exit.txt')).write_text(str(v.returncode)+'\n')
 REPORT['steps'].append({'name':name,'exit_code':v.returncode,'elapsed_seconds':time.monotonic()-t});print(json.dumps(REPORT['steps'][-1]),flush=True)
 if v.returncode!=0:raise RuntimeError(name+' failed: '+v.stdout[-1600:])
 return v.stdout
try:
 prefix='papers/flat-coarse-rank/integrated-revision/'
 tex=fetch('lluiseriksson/THE-ERIKSSON-PROGRAMME',args.source_sha,prefix+'revision136/flat_critical_integrated.tex')
 if hashlib.sha256(tex).hexdigest()!='2f3584253453cdab1507f91ff6cc755374f233daf9e6236a2b274a37e1c5a12f':raise ValueError('Source hash')
 (OUT/'flat_critical_integrated.tex').write_bytes(tex)
 for name in ('source-context.json',): (OUT/name).write_bytes(fetch('lluiseriksson/THE-ERIKSSON-PROGRAMME',args.source_sha,prefix+'revision136/'+name))
 for name in ('main-declaration-map.json','critical-declaration-map.json','integration-map.json'):(OUT/name).write_bytes(fetch('lluiseriksson/THE-ERIKSSON-PROGRAMME',args.source_sha,prefix+name))
 review=OUT/'prior-v5-review'; review.mkdir()
 for name in ('assessment.json','model-response-original.txt','model-response.json','request.txt','review-context.json','OPERATOR-RESPONSE.md'):
  (review/name).write_bytes(fetch('arr-research/arr-research.github.io','bd2b690287a92d5632627436d54fc5c8300d0d17','registry/assessment-evidence/2026-11-05-eriksson-v5-gemini/'+name))
 (OUT/'render136.py').write_bytes(pathlib.Path(__file__).read_bytes())
 run('apt-update',['apt-get','update','-qq']);run('apt-install',['apt-get','install','-y','-qq','texlive-latex-recommended','texlive-fonts-recommended','lmodern','poppler-utils'])
 for k in (1,2):run('pdflatex-pass'+str(k),['pdflatex','-interaction=nonstopmode','-halt-on-error','flat_critical_integrated.tex'])
 info=run('pdfinfo',['pdfinfo','flat_critical_integrated.pdf']);run('pdftotext',['pdftotext','-layout','flat_critical_integrated.pdf','paper.txt'])
 warnings=[s for s in (OUT/'flat_critical_integrated.log').read_text(errors='replace').splitlines() if any(v in s for v in ('Overfull','Underfull','LaTeX Warning'))]
 REPORT['warnings']=warnings
 if any('Overfull' in s or 'undefined' in s.lower() or 'multiply defined' in s.lower() for s in warnings):raise ValueError('Layout or reference warning')
 pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M)[1]);run('render-pages',['pdftoppm','-r','100','-png','flat_critical_integrated.pdf','page'])
 if not 25<=pages<=45 or len(list(OUT.glob('page-*.png')))!=pages:raise ValueError('Page count')
 REPORT.update(status='RENDERED_AWAITING_FULL_VISUAL_REVIEW_AND_FIRST_EXACT_ASSESSMENT',pages=pages,pdf_sha256=digest(OUT/'flat_critical_integrated.pdf'),finished_utc=datetime.now(timezone.utc).isoformat())
except Exception as exc:
 REPORT.update(status='FAILED',error=str(exc),traceback=traceback.format_exc(),finished_utc=datetime.now(timezone.utc).isoformat())
finally:
 (OUT/'render-report.json').write_text(json.dumps(REPORT,indent=2))
 manifest={str(f.relative_to(OUT)):digest(f) for f in sorted(OUT.rglob('*')) if f.is_file()}
 (OUT/'SHA256.json').write_text(json.dumps(manifest,indent=2))
 with zipfile.ZipFile(ROOT/'revision136-evidence.zip','w',zipfile.ZIP_DEFLATED) as z:
  for f in sorted(OUT.rglob('*')):
   if f.is_file():z.write(f,str(f.relative_to(OUT)))
 print(json.dumps({'report':REPORT,'zip_sha256':digest(ROOT/'revision136-evidence.zip'),'zip_bytes':(ROOT/'revision136-evidence.zip').stat().st_size}),flush=True)
 if REPORT['status']=='FAILED':raise SystemExit(1)
