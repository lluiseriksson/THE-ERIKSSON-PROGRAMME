import json,hashlib
SOURCE='7822ac91245a8e79c304e595ca82b786283c3c92'
INPUTS={'boundary-transfer.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/boundary-transfer.tex', 'sha256': 'b212df92560d7ae3f6f3bd3d2f8619f26172b478c008737d099adf30f9cc86e0'}, 'detour-separation.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/detour-separation.tex', 'sha256': 'd56fbeaee52e210110e11e87597c7f8ce25d3d46aeeab9d7455588082bc160a8'}, 'flat_critical_integrated.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/flat_critical_integrated.tex', 'sha256': 'b33485504fdaf390b14fd3a56e85ff7b11108b358aec120a38df67887a050d6b'}, 'geometry-boundaries221.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/geometry-boundaries221.tex', 'sha256': 'ee03c649af2bcc8cf22d4f152a68517d84795f7fab64a48451887c89f2b36e09'}, 'joint-binary.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/joint-binary.tex', 'sha256': '001f9e6d2ec168fac732baad166f8ab2dc876bab84b82c00b8df75385e532551'}, 'laminates-green.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/laminates-green.tex', 'sha256': '3aa2b0517c400aef0259a353b3d04f0750a4af3d6390d31989bcc1616e236ab1'}, 'partial-invariance.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/partial-invariance.tex', 'sha256': 'fd2c382bda872858a71b0dc0fd992ce58a509e139e13d5f930de0a59bce50a01'}, 'partition.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/partition.tex', 'sha256': 'b76593ea452f24ef7c206a9c61cab4a9c35dd7425d95d8f28bf77134d1a9cfff'}, 'physical-cycle.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/physical-cycle.tex', 'sha256': 'c06cfc76e02a7c50a83d7f9dbad0fb2b92f23440f330339a16c533fb4494917c'}, 'shells.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/shells.tex', 'sha256': '646c65637664d98af18d58d914c312743b1cff77a5d6db99e2a51e0af0bc6f4a'}, 'sobolev.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/sobolev.tex', 'sha256': '80c4a34aaa9ba9ff840e195ddee32a2f3af7201e9d05f51243130bf571b12a54'}, 'spatial-geometry.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision221/spatial-geometry.tex', 'sha256': '3f6152b40718190276160977a3401f52ad910a5f150890c971be01c1a1bfd4f9'}}
import os,sys,time,traceback,subprocess,resource,zipfile,urllib.request
from datetime import datetime,timezone
from pathlib import Path
if not Path('/content').is_dir():raise RuntimeError('Own Colab Linux required')
out=Path('/content/tep221A');out.mkdir(exist_ok=False);os.chdir(out)
start=time.monotonic();report={'source_sha':SOURCE,'source_inputs':INPUTS,'started_utc':datetime.now(timezone.utc).isoformat(),'tool_exits':{},'compute_units_billed':None,'formal_or_scientific_replay':False}
def run(args,name,timeout=240):
 p=subprocess.run(args,capture_output=True,timeout=timeout)
 (out/(name+'.stdout')).write_bytes(p.stdout);(out/(name+'.stderr')).write_bytes(p.stderr)
 tmp=out/(name+'.exit.tmp');tmp.write_text(str(p.returncode)+'\n');code=int(tmp.read_text().strip());os.replace(tmp,out/(name+'.exit'));report['tool_exits'][name]=code
 if code:raise RuntimeError(name+' exited '+str(code))
 return p.stdout.decode(errors='replace')
try:
 for name,spec in INPUTS.items():
  raw=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/'+spec['path'],timeout=45).read()
  if hashlib.sha256(raw).hexdigest()!=spec['sha256']:raise RuntimeError('Input hash mismatch '+name)
  (out/name).write_bytes(raw)
 run(['apt-get','-qq','update'],'apt-update',600)
 run(['apt-get','install','-y','-qq','texlive-latex-base','texlive-latex-recommended','texlive-fonts-recommended','lmodern','poppler-utils'],'apt-install',900)
 os.environ['SOURCE_DATE_EPOCH']='1794182400';os.environ['FORCE_SOURCE_DATE']='1'
 report['tex_version']=run(['pdflatex','--version'],'tex-version')
 run(['pdftoppm','-v'],'poppler-version');report['poppler_version']=(out/'poppler-version.stderr').read_text()
 for stage in ['first','second','final']:run(['pdflatex','-interaction=nonstopmode','-halt-on-error','flat_critical_integrated.tex'],'latex-'+stage)
 report['pdfinfo']=run(['pdfinfo','flat_critical_integrated.pdf'],'pdfinfo')
 run(['pdftotext','-layout','flat_critical_integrated.pdf','flat_critical_integrated.txt'],'text')
 joined=' '.join((out/'flat_critical_integrated.txt').read_text().split())
 for expected in ['Model assessments and review context','Selected shell observations and geometric limits','7350','2592','1680']:
  if expected not in joined:raise RuntimeError('Missing current content '+expected)
 log=(out/'flat_critical_integrated.log').read_text(errors='replace');warnings=[x for x in log.splitlines() if any(s in x for s in ['Overfull','Undefined','undefined references','LaTeX Warning'])];report['layout_warnings']=warnings
 run(['pdftoppm','-r','110','-png','flat_critical_integrated.pdf','page'],'render')
 from PIL import Image,ImageDraw
 pages=sorted(out.glob('page-*.png'))
 if not pages:raise RuntimeError('No exact PDF pages')
 for block,offset in enumerate(range(0,len(pages),6),1):
  sheet=Image.new('RGB',(840,1740),'#dddddd')
  for i,page in enumerate(pages[offset:offset+6]):
   with Image.open(page) as im:
    im=im.convert('RGB');im.thumbnail((400,540));sheet.paste(im,((i%2)*420+(420-im.width)//2,(i//2)*580+10))
   ImageDraw.Draw(sheet).text(((i%2)*420+10,(i//2)*580+558),page.name,fill='black')
  sheet.save(out/('contact-'+str(block).zfill(2)+'.jpg'),quality=90)
 pdf=out/'flat_critical_integrated.pdf';report.update(status='RENDERED_PENDING_VISUAL_REVIEW',pages=len(pages),pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),pdf_bytes=pdf.stat().st_size)
 if warnings:raise RuntimeError('Final layout warnings preserved')
except Exception:
 report['status']='FAILED_PRESERVED';(out/'failure.txt').write_text(traceback.format_exc())
finally:
 report.update(finished_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-start,child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
 (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 manifest=[{'path':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(out.iterdir()) if p.is_file()]
 (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 zpath=Path('/content/tep221A-review.zip')
 with zipfile.ZipFile(zpath,'w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(out.iterdir()):
   if p.is_file():z.write(p,p.name)
 print(json.dumps(report));print('ZIP_SHA256='+hashlib.sha256(zpath.read_bytes()).hexdigest())
 if report['status']=='FAILED_PRESERVED':sys.exit(1)
