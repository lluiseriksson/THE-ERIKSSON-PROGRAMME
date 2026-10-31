import os,sys,json,time,pathlib,subprocess,hashlib,urllib.request,zipfile,base64,traceback
from datetime import datetime,timezone
SHA='8f333c6458de613e6eab69a3de92c9c5dff9a2dc'
EXPECTED='0a0e06d67a3e2b28376d620a78128c2c1d045cb68a0381fedce782d3f8a6bf6a'
ROOT=pathlib.Path('/content/eriksson-render056');ROOT.mkdir(exist_ok=True)
OUT=ROOT/'evidence';OUT.mkdir(exist_ok=True)
report={'source_sha':SHA,'started_utc':datetime.now(timezone.utc).isoformat(),'steps':[],'status':'PENDING','independent_review':False}
def digest(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def run(name,args):
 t=time.monotonic();p=subprocess.run(args,cwd=OUT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env=dict(os.environ,DEBIAN_FRONTEND='noninteractive',SOURCE_DATE_EPOCH='1793332800',FORCE_SOURCE_DATE='1',TZ='UTC'))
 (OUT/(name+'.log')).write_text(p.stdout)
 item={'name':name,'exit_code':p.returncode,'seconds':round(time.monotonic()-t,6)};report['steps'].append(item);print(json.dumps(item),flush=True)
 if p.returncode:raise RuntimeError(name+' failed: '+p.stdout[-2200:])
 return p.stdout
try:
 url='https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SHA+'/papers/flat-coarse-rank/v4-candidate/flat_coarse_rank.tex'
 source=urllib.request.urlopen(url).read()
 if hashlib.sha256(source).hexdigest()!=EXPECTED:raise ValueError('source digest mismatch')
 (OUT/'flat_coarse_rank.tex').write_bytes(source)
 run('apt-update',['apt-get','update','-qq'])
 run('apt-install',['apt-get','install','-y','-qq','texlive-latex-recommended','texlive-fonts-recommended','lmodern','poppler-utils','nodejs'])
 run('pip-render',['python','-m','pip','install','-q','PyMuPDF==1.26.7'])
 run('pdflatex-pass1',['pdflatex','-interaction=nonstopmode','-halt-on-error','flat_coarse_rank.tex'])
 run('pdflatex-pass2',['pdflatex','-interaction=nonstopmode','-halt-on-error','flat_coarse_rank.tex'])
 run('pdfinfo',['pdfinfo','flat_coarse_rank.pdf'])
 run('pdftotext',['pdftotext','-layout','flat_coarse_rank.pdf','flat_coarse_rank.txt'])
 run('pdftoppm',['pdftoppm','-r','110','-jpeg','-jpegopt','quality=84','flat_coarse_rank.pdf','page'])
 import fitz
 from PIL import Image,ImageOps,ImageDraw
 pdf=fitz.open(OUT/'flat_coarse_rank.pdf');report['pages']=len(pdf);report['pdf_sha256']=digest(OUT/'flat_coarse_rank.pdf');report['source_sha256']=EXPECTED
 if len(pdf)<4:raise ValueError('unexpected short manuscript')
 imgs=sorted(OUT.glob('page-*.jpg'))
 if len(imgs)!=len(pdf):raise ValueError('rendered page count mismatch')
 for start in range(0,len(imgs),4):
  sheet=Image.new('RGB',(1200,1680),'#dddddd');draw=ImageDraw.Draw(sheet)
  for i,p in enumerate(imgs[start:start+4]):
   im=Image.open(p);im.thumbnail((580,790));x=(i%2)*600+(600-im.width)//2;y=(i//2)*840+34
   sheet.paste(im,(x,y));draw.text(((i%2)*600+18,(i//2)*840+12),'Page '+str(start+i+1),fill='black')
  sheet.save(OUT/('contact-'+str(start+1)+'.jpg'),quality=88)
 log=(OUT/'flat_coarse_rank.log').read_text(errors='replace');report['layout_warnings']=[l for l in log.splitlines() if 'Overfull' in l or 'Underfull' in l or 'LaTeX Warning' in l]
 (OUT/'tool-versions.txt').write_text(subprocess.getoutput('pdflatex --version')+'\n'+subprocess.getoutput('pdftoppm -v')+'\nPyMuPDF '+fitz.VersionBind)
 report['status']='PDF_COMPILED_ALL_PAGES_RENDERED_AWAITING_VISUAL_QA'
except Exception as e:
 report['status']='FAILED';report['error']=str(e);(OUT/'exception.txt').write_text(traceback.format_exc())
finally:
 report['finished_utc']=datetime.now(timezone.utc).isoformat();(OUT/'report.json').write_text(json.dumps(report,indent=2))
 manifest={p.name:digest(p) for p in sorted(OUT.iterdir()) if p.is_file()};(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2))
 z=ROOT/'render056.zip'
 with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as f:
  for p in sorted(OUT.iterdir()):
   if p.is_file():f.write(p,p.name)
 print('FINAL_REPORT='+json.dumps(report),flush=True);print('BUNDLE_SHA256='+digest(z),flush=True)
 print('EVIDENCE_BASE64_BEGIN='+base64.b64encode(z.read_bytes()).decode()+'=EVIDENCE_BASE64_END',flush=True)
 print('INLINE_EVIDENCE_EMITTED; releasing runtime.',flush=True)
 from google.colab import runtime
 runtime.unassign()
