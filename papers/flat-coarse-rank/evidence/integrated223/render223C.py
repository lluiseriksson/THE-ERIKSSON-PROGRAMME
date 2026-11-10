import json,hashlib
SOURCE='ddd2cf605c1715a03d2e87991e920c0ec760e527'
INPUTS={'balanced-rings223.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/balanced-rings223.tex', 'sha256': '6877841cde546f8920c39b98a5dfef8af385b1a2d5a4842f95a9dd36985b3dc2'}, 'boundary-transfer.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/boundary-transfer.tex', 'sha256': 'e3d1b9fc6a642c0ac68dfdd3bccda442bfe25ae63e2a8ee713cea12fd5fcd155'}, 'detour-separation.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/detour-separation.tex', 'sha256': 'd56fbeaee52e210110e11e87597c7f8ce25d3d46aeeab9d7455588082bc160a8'}, 'flat_critical_integrated.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/flat_critical_integrated.tex', 'sha256': '2b916abb82de709f52a9671fa3f1e9c6019bf2224127c2c111ac1de6cab1acc6'}, 'geometry-boundaries221.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/geometry-boundaries221.tex', 'sha256': 'b2bb2dfb39538ce05eac0a6835ef4534491e514219a165cb9d634a9383577a50'}, 'joint-binary.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/joint-binary.tex', 'sha256': '084213b6b6fb6f864b82e2bfa0551775cce878ea9a1b0054eb30ab77e83d6c6c'}, 'laminates-green.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/laminates-green.tex', 'sha256': '4a573061166dcb39824bea1aaf8a8e237dbcf2ab4a7c19be57e54cff02d13b55'}, 'partial-invariance.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/partial-invariance.tex', 'sha256': 'bba932a34bef4ac01ca24047487a0fab5cb3e98c6dc3e010041e7b5d91a5cda7'}, 'partition.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/partition.tex', 'sha256': 'b76593ea452f24ef7c206a9c61cab4a9c35dd7425d95d8f28bf77134d1a9cfff'}, 'physical-cycle.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/physical-cycle.tex', 'sha256': 'c06cfc76e02a7c50a83d7f9dbad0fb2b92f23440f330339a16c533fb4494917c'}, 'shells.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/shells.tex', 'sha256': '646c65637664d98af18d58d914c312743b1cff77a5d6db99e2a51e0af0bc6f4a'}, 'sobolev.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/sobolev.tex', 'sha256': '1cb480d4d67b67e4e1e4181c391f620bf21c2558fe4002f239e149eaa81bf712'}, 'spatial-geometry.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision223/spatial-geometry.tex', 'sha256': '3e658054bca885ec7bd2f018b33c1f122e54f3038c39282279fa61e9a9ac7a2b'}}
import os,sys,time,traceback,subprocess,resource,zipfile,urllib.request
from datetime import datetime,timezone
from pathlib import Path
if not Path('/content').is_dir():raise RuntimeError('Own Colab Linux required')
out=Path('/content/tep223C');out.mkdir(exist_ok=False);os.chdir(out)
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
 for expected in ['Model assessments and review context','Coefficient-selected rectangular means for arbitrary scalar profiles','7350','2592','1680']:
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
 zpath=Path('/content/tep223C-review.zip')
 with zipfile.ZipFile(zpath,'w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(out.iterdir()):
   if p.is_file():z.write(p,p.name)
 print(json.dumps(report));print('ZIP_SHA256='+hashlib.sha256(zpath.read_bytes()).hexdigest())
 if report['status']=='FAILED_PRESERVED':sys.exit(1)
