import json,hashlib
SOURCE='2d3237501569f6afac8a44d524a5d6db59f63c39'
INPUTS={'common-rank.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision226/common-rank.tex', 'sha256': '350550313a26186fc99b26dbfa09880e6cf05702b2a7c09f3eb8bb4af0069c0b'}, 'matrix-proof.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision226/matrix-proof.tex', 'sha256': '9e5887ed4c59204d12c0f86adc97798ec45281e3eb2473d38dc26e0153b469c8'}, 'rectangular_matrix.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision226/rectangular_matrix.tex', 'sha256': '3ba36a34ad5d3c4a759e100ad0e9db14c9c20a7b07829ceaaa2453038b315eb3'}, 'review-context.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision226/review-context.tex', 'sha256': '9be1438be6ec128f6852faa1affa6f85a6c6ca9e9a4570a84a20f676b21dbd57'}, 'scalar-rings.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision226/scalar-rings.tex', 'sha256': 'ccd5279b9ab02e9a336bfb828fec3b9a35415583205ccb7dfa0189e624d249f0'}, 'weak-endpoint.tex': {'path': 'papers/flat-coarse-rank/integrated-revision/revision226/weak-endpoint.tex', 'sha256': '6f753c5b0105a594b30a18b4d8725eea3503bc28565dd5bc678eedc506f3d8e7'}}
import os,sys,time,traceback,subprocess,resource,zipfile,urllib.request
from datetime import datetime,timezone
from pathlib import Path
if not Path('/content').is_dir():raise RuntimeError('Own Colab Linux required')
out=Path('/content/tep226C');out.mkdir(exist_ok=False);os.chdir(out)
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
 run(['apt-get','install','-y','-qq','texlive-latex-base','texlive-latex-recommended','texlive-latex-extra','texlive-fonts-recommended','lmodern','poppler-utils'],'apt-install',900)
 os.environ['SOURCE_DATE_EPOCH']='1794182400';os.environ['FORCE_SOURCE_DATE']='1'
 report['tex_version']=run(['pdflatex','--version'],'tex-version')
 run(['pdftoppm','-v'],'poppler-version');report['poppler_version']=(out/'poppler-version.stderr').read_text()
 for stage in ['first','second','final']:run(['pdflatex','-interaction=nonstopmode','-halt-on-error','rectangular_matrix.tex'],'latex-'+stage)
 report['pdfinfo']=run(['pdfinfo','rectangular_matrix.pdf'],'pdfinfo')
 run(['pdftotext','-layout','rectangular_matrix.pdf','rectangular_matrix.txt'],'text')
 joined=' '.join((out/'rectangular_matrix.txt').read_text().split())
 for expected in ['Rectangular observations for finite matrix gradients','Model assessments and review context','common','weak']:
  if expected not in joined:raise RuntimeError('Missing current content '+expected)
 log=(out/'rectangular_matrix.log').read_text(errors='replace');warnings=[x for x in log.splitlines() if any(s in x for s in ['Overfull','Undefined','undefined references','LaTeX Warning'])];report['layout_warnings']=warnings
 run(['pdftoppm','-r','110','-png','rectangular_matrix.pdf','page'],'render')
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
 pdf=out/'rectangular_matrix.pdf';report.update(status='RENDERED_PENDING_VISUAL_REVIEW',pages=len(pages),pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),pdf_bytes=pdf.stat().st_size)
 if warnings:raise RuntimeError('Final layout warnings preserved')
except Exception:
 report['status']='FAILED_PRESERVED';(out/'failure.txt').write_text(traceback.format_exc())
finally:
 report.update(finished_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-start,child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
 (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 manifest=[{'path':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(out.iterdir()) if p.is_file()]
 (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 zpath=Path('/content/tep226C-review.zip')
 with zipfile.ZipFile(zpath,'w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(out.iterdir()):
   if p.is_file():z.write(p,p.name)
 print(json.dumps(report));print('ZIP_SHA256='+hashlib.sha256(zpath.read_bytes()).hexdigest())
 if report['status']=='FAILED_PRESERVED':sys.exit(1)
