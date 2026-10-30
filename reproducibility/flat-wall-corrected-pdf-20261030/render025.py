import os,sys,json,time,pathlib,subprocess,hashlib,urllib.request,zipfile,base64,traceback
from datetime import datetime,timezone
SHA='ac066118d29176050518cd2cdea0f7c4a98ea040'
EXPECTED='d850da3f440cf6bc791de810f0e2ba15ebf642b7b8c92269b1528b02062df244'
ROOT=pathlib.Path('/content/eriksson-render025');ROOT.mkdir(exist_ok=True)
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
 url='https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SHA+'/papers/flat-coarse-rank/flat_coarse_rank.tex'
 source=urllib.request.urlopen(url).read()
 if hashlib.sha256(source).hexdigest()!=EXPECTED:raise ValueError('source digest mismatch')
 (OUT/'flat_coarse_rank.tex').write_bytes(source)
 run('apt-update',['apt-get','update','-qq'])
 run('apt-install',['apt-get','install','-y','-qq','texlive-latex-recommended','texlive-fonts-recommended','lmodern','poppler-utils','nodejs'])
 run('pip-render',['python','-m','pip','install','-q','PyMuPDF==1.26.7'])
 marker=base64.b64decode("IyEvdXNyL2Jpbi9lbnYgbm9kZQ0KDQpjb25zdCBhcmdzID0gcHJvY2Vzcy5hcmd2LnNsaWNlKDIpOw0KY29uc3QgZXhwZWN0ZWRPdXRwdXRDb3VudCA9IE51bWJlcihhcmdzWzNdKTsNCmNvbnN0IHZhbGlkT3V0cHV0Rm9ybWF0cyA9IG5ldyBTZXQoWyJwZGYiXSk7DQpjb25zdCB2YWxpZCA9DQogIGFyZ3MubGVuZ3RoID09PSA2ICYmDQogIGFyZ3NbMF0gPT09ICItLW9wZXJhdGlvbi1raW5kIiAmJg0KICBuZXcgU2V0KFsiY3JlYXRlIiwgImVkaXQiXSkuaGFzKGFyZ3NbMV0pICYmDQogIGFyZ3NbMl0gPT09ICItLWV4cGVjdGVkLW91dHB1dC1jb3VudCIgJiYNCiAgTnVtYmVyLmlzU2FmZUludGVnZXIoZXhwZWN0ZWRPdXRwdXRDb3VudCkgJiYNCiAgZXhwZWN0ZWRPdXRwdXRDb3VudCA+PSAxICYmDQogIGV4cGVjdGVkT3V0cHV0Q291bnQgPD0gMTAwICYmDQogIGFyZ3NbNF0gPT09ICItLW91dHB1dC1mb3JtYXQiICYmDQogIHZhbGlkT3V0cHV0Rm9ybWF0cy5oYXMoYXJnc1s1XS50b0xvd2VyQ2FzZSgpKTsNCg0KaWYgKCF2YWxpZCkgew0KICBjb25zb2xlLmVycm9yKA0KICAgICJ1c2FnZTogbWFya19hcnRpZmFjdF9vcGVyYXRpb25fc3RhcnRlZC5tanMgLS1vcGVyYXRpb24ta2luZCA8Y3JlYXRlfGVkaXQ+IC0tZXhwZWN0ZWQtb3V0cHV0LWNvdW50IDwxLTEwMD4gLS1vdXRwdXQtZm9ybWF0IDxzdXBwb3J0ZWQgZm9ybWF0PiIsDQogICk7DQogIHByb2Nlc3MuZXhpdENvZGUgPSAyOw0KfQ0K").decode("utf-8")
 (OUT/'mark_artifact_operation_started.mjs').write_text(marker)
 run('artifact-operation-marker',['node','mark_artifact_operation_started.mjs','--operation-kind','edit','--expected-output-count','1','--output-format','pdf'])
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
 z=ROOT/'render025.zip'
 with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as f:
  for p in sorted(OUT.iterdir()):
   if p.is_file():f.write(p,p.name)
 print('FINAL_REPORT='+json.dumps(report),flush=True);print('BUNDLE_SHA256='+digest(z),flush=True)
 print('EVIDENCE_BASE64_BEGIN='+base64.b64encode(z.read_bytes()).decode()+'=EVIDENCE_BASE64_END',flush=True)
 print('INLINE_EVIDENCE_EMITTED; releasing runtime.',flush=True)
 from google.colab import runtime
 runtime.unassign()
