# Colab Linux only. One fresh clone; not terminal paired reproduction.
import argparse,pathlib,subprocess,sys,os,time,json,re,hashlib,traceback,zipfile,urllib.request
from datetime import datetime,timezone
p=argparse.ArgumentParser();p.add_argument('--source-sha',required=True);a=p.parse_args()
if not sys.platform.startswith('linux'):raise RuntimeError('Colab Linux only')
ROOT=pathlib.Path('/content/tep-cycle147');ROOT.mkdir(exist_ok=False);OUT=ROOT/'evidence';OUT.mkdir();clone=ROOT/'fresh';ENV=dict(os.environ);ENV['PATH']=str(pathlib.Path.home()/'.elan/bin')+':'+ENV['PATH']
report={'unit':147,'source_sha':a.source_sha,'started_utc':datetime.now(timezone.utc).isoformat(),'status':'RUNNING','steps':[],'terminal_paired_reproduction':False,'longitudinal_kernel_coercivity_verified':False,'full_kernel_coercivity_Lean_verified':False}
names=['actualCycleKernel_profile_pair_zero','actualCycleKernel_fibre_coercive','actualCycleFibre_norm_decomposition','actualCycleKernel_coordinate_sum_coercive','actualCycleKernel_norm_coercive']
VALIDATOR=r'''
import sys,pathlib,json,re
NAMES=['actualCycleKernel_profile_pair_zero','actualCycleKernel_fibre_coercive','actualCycleFibre_norm_decomposition','actualCycleKernel_coordinate_sum_coercive','actualCycleKernel_norm_coercive']
PAT=r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def verify(raw):
 hits=list(re.finditer(PAT,raw))
 if len(hits)!=5:raise ValueError('five actual oracle outputs required')
 rows=[]
 for hit,name in zip(hits,NAMES):
  nm,axes=hit.groups();axs=[s.strip() for s in (axes or '').split(',') if s.strip()]
  if nm!='YangMills.RG.'+name or len(axs)!=len(set(axs)) or not set(axs)<={'propext','Classical.choice','Quot.sound'}:raise ValueError('unexpected endpoint/dependency')
  rows.append({'name':nm,'axioms':axs})
 return rows
raw=pathlib.Path(sys.argv[1]).read_text();rows=verify(raw);hit=list(re.finditer(PAT,raw))[0]
mutations=[raw[:hit.start()]+raw[hit.end():],raw.replace(hit.group(1),'Wrong.Endpoint',1),raw[:hit.start()]+"'"+hit.group(1)+"' depends on axioms: [sorryAx]"+raw[hit.end():]]
rejected=0
for bad in mutations:
 if bad==raw:raise RuntimeError('mutation unchanged')
 try:verify(bad)
 except ValueError:rejected+=1
 else:raise RuntimeError('accepted mutated actual oracle')
if len(rows)!=5 or rejected!=3:raise RuntimeError('explicit oracle counters')
print(json.dumps({'status':'ORACLE_PASS','accepted':5,'actual_mutations_rejected':3,'rows':rows},sort_keys=True))
'''
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def run(name,cmd,cwd=None,timeout=1200):
 t=time.monotonic();log=OUT/(name+'.log')
 with log.open('w') as f:r=subprocess.run(cmd,cwd=cwd,env=ENV,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
 tmp=OUT/(name+'.exit.tmp');tmp.write_text(str(r.returncode)+'\n');need(re.fullmatch(r'-?\d+\n',tmp.read_text()) is not None,'sentinel');tmp.replace(OUT/(name+'.exit.txt'))
 report['steps'].append({'name':name,'exit':r.returncode,'seconds':time.monotonic()-t});print(json.dumps(report['steps'][-1]),flush=True)
 need(r.returncode==0,name+' failed: '+log.read_text(errors='replace')[-8000:]);return log
try:
 if not (pathlib.Path.home()/'.elan/bin/elan').exists():
  installer=OUT/'elan-init.sh';urllib.request.urlretrieve('https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh',installer);run('install-elan',['bash',str(installer),'-y','--default-toolchain','none'],timeout=600)
 run('init',['git','init',str(clone)],timeout=60);run('remote',['git','remote','add','origin','https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git'],clone,60)
 for key,value in [('core.autocrlf','false'),('core.sparseCheckout','true'),('remote.origin.promisor','true'),('remote.origin.partialclonefilter','blob:none')]:run('config-'+key,['git','config',key,value],clone,60)
 (clone/'.git/info/sparse-checkout').write_text('/lean-toolchain\n/lakefile.lean\n/lake-manifest.json\n*.lean\n')
 run('fetch',['git','fetch','--depth=1','--filter=blob:none','origin',a.source_sha],clone,300);run('checkout',['git','checkout','--detach','FETCH_HEAD'],clone,300)
 need(run('head',['git','rev-parse','HEAD'],clone,60).read_text().strip()==a.source_sha,'wrong clone')
 need((clone/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.29.0-rc6','toolchain')
 manifest=json.loads((clone/'lake-manifest.json').read_text());need([x['rev'] for x in manifest['packages'] if x['name']=='mathlib']==['07642720480157414db592fa85b626dafb71355b'],'mathlib pin')
 for f in ('PhysicalCycleKernel.lean','PhysicalCycleKernelOracle.lean'):
  data=(clone/'YangMills/RG'/f).read_bytes();(OUT/f).write_bytes(data)
  need(not re.search(rb'\b(sorry|axiom)\b',data),'candidate sorry/axiom token')
 run('lean-version',['lean','--version'],clone,600)
 # Same official version/URL used by pinned Mathlib; bounded HTTP-error retries.
 asset=OUT/'leantar-0.1.16.tar.gz';cache=pathlib.Path.home()/'.cache/mathlib';cache.mkdir(parents=True,exist_ok=True)
 url='https://github.com/digama0/leangz/releases/download/v0.1.16/leantar-v0.1.16-x86_64-unknown-linux-musl.tar.gz'
 run('leantar-download',['curl','--fail','--retry','3','--retry-all-errors','--retry-delay','2','--max-time','90','-L',url,'-o',str(asset)],timeout=420)
 need(asset.read_bytes().startswith(b'\x1f\x8b'),'official asset is not gzip')
 report['leantar_asset_sha256']=sha(asset)
 run('leantar-extract',['tar','-xzf',str(asset),'-C',str(cache),'--strip-components=1'],timeout=60)
 (cache/'leantar').replace(cache/'leantar-0.1.16')
 run('leantar-version',[str(cache/'leantar-0.1.16'),'--version'],timeout=60)
 run('mathlib-cache',['lake','exe','cache','get'],clone,1800)
 run('build',['lake','build','YangMills.RG.PhysicalCycleKernel'],clone,1200)
 oracle=run('oracle',['lake','env','lean','YangMills/RG/PhysicalCycleKernelOracle.lean'],clone,300)
 validator=OUT/'oracle-validator.py';validator.write_text(VALIDATOR);results=[]
 for mode,flags in [('normal',[]),('optimized',['-O'])]:
  log=run('validator-'+mode,[sys.executable]+flags+[str(validator),str(oracle)],clone,120);val=json.loads(log.read_text());need(val['status']=='ORACLE_PASS' and val['accepted']==5 and val['actual_mutations_rejected']==3,'counters');results.append(val)
 need(results[0]==results[1],'oracle mode outputs differ')
 olean=clone/'.lake/build/lib/lean/YangMills/RG/PhysicalCycleKernel.olean';need(olean.is_file(),'missing olean');(OUT/'PhysicalCycleKernel.olean').write_bytes(olean.read_bytes())
 report.update(status='FIVE_KERNEL_FIBRE_ENDPOINTS_FIRST_CLONE_PASS',longitudinal_kernel_coercivity_verified=True,full_physical_norm_decomposition_verified=True,endpoints=results[0]['rows'],olean_sha256=sha(olean),oracle_sha256=sha(oracle))
except Exception as e:report.update(status='FAILED',error=str(e),traceback=traceback.format_exc())
finally:
 report['finished_utc']=datetime.now(timezone.utc).isoformat();(OUT/'report.json').write_text(json.dumps(report,indent=2));(OUT/'build147.py').write_bytes(pathlib.Path(__file__).read_bytes())
 (OUT/'SHA256.json').write_text(json.dumps({str(f.relative_to(OUT)):sha(f) for f in OUT.rglob('*') if f.is_file()},indent=2))
 zpath=pathlib.Path('/content/tep-cycle147.zip')
 with zipfile.ZipFile(zpath,'w',zipfile.ZIP_DEFLATED) as z:
  for f in sorted(OUT.rglob('*')):
   if f.is_file():z.write(f,str(f.relative_to(OUT)))
 print(json.dumps({'status':report['status'],'zip_bytes':zpath.stat().st_size,'zip_sha256':sha(zpath)}),flush=True)
 if report['status']=='FAILED':raise SystemExit(1)
