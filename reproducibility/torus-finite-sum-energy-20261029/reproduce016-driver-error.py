import os, sys, json, re, time, hashlib, subprocess, pathlib, zipfile, traceback, urllib.request
from datetime import datetime, timezone
SHA='251401e4de885dd0d70905e32da01bf5ba40cffd'
EXPECTED=json.loads(r'''{"TorusFiniteSumEnergy.lean":"d827d30fb331b376f9b04ab36f2fc515170dabfe7a090e2c30e8aa07ae670260","TorusFiniteSumEnergyOracle.lean":"263205106055be0879f28cfb05d27d88a7f7bb804ab68596fc3816c1a0aed2d9"}''')
ROOT=pathlib.Path('/content/eriksson-paper47-20261029-016')
OUT=pathlib.Path('/content/eriksson-paper47-evidence-016')
OUT.mkdir(exist_ok=False)
REPORT={'schema':1,'source_sha':SHA,'started_utc':datetime.now(timezone.utc).isoformat(),'steps':[],'status':'RUNNING','independent_review':False}
ENV=os.environ.copy(); ENV['PATH']=str(pathlib.Path.home()/'.elan/bin')+':'+ENV['PATH']
def run(name,args,cwd=None,limit=7200):
    start=time.time(); log=OUT/(name+'.log')
    with log.open('w') as f:
        p=subprocess.run(args,cwd=cwd,env=ENV,stdout=f,stderr=subprocess.STDOUT,timeout=limit)
    row={'name':name,'exit_code':p.returncode,'seconds':round(time.time()-start,3),'log':log.name}
    REPORT['steps'].append(row); print(json.dumps(row),flush=True)
    if p.returncode!=0: raise RuntimeError(name+' failed: '+log.read_text(errors='replace')[-5000:])
    return log
try:
    if not pathlib.Path('/root/.elan/bin/lake').exists():
        installer=OUT/'elan-init.sh'
        urllib.request.urlretrieve('https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh',installer)
        run('install-elan',['bash',str(installer),'-y','--default-toolchain','none'],limit=600)
    ROOT.mkdir(exist_ok=False)
    run('git-init',['git','init'],ROOT)
    run('git-remote',['git','remote','add','origin','https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git'],ROOT)
    run('git-fetch',['git','fetch','--depth=1','origin',SHA],ROOT)
    run('git-checkout',['git','checkout','--detach','FETCH_HEAD'],ROOT)
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    if actual!=SHA: raise RuntimeError('Wrong source SHA')
    hashes=[]
    for name,want in EXPECTED.items():
        data=(ROOT/'YangMills/RG'/name).read_bytes().replace(b'\r\n',b'\n')
        got=hashlib.sha256(data).hexdigest()
        hashes.append({'name':name,'sha256_lf':got,'expected':want,'matches':got==want})
        if got!=want: raise RuntimeError('Source mismatch: '+name)
    if len(hashes)!=2: raise RuntimeError('Expected two sources')
    (OUT/'source-hashes.json').write_text(json.dumps(hashes,indent=2))
    toolchain=(ROOT/'lean-toolchain').read_text().strip()
    if toolchain!='leanprover/lean4:v4.29.0-rc6': raise RuntimeError('Unexpected toolchain '+toolchain)
    manifest=json.loads((ROOT/'lake-manifest.json').read_text())
    mathlib=[p for p in manifest['packages'] if p['name']=='mathlib']
    if len(mathlib)!=1 or mathlib[0]['rev']!='07642720480167414db592fa85b626dafb71355b': raise RuntimeError('Mathlib pin mismatch')
    run('lean-version',['lean','--version'],ROOT,600)
    run('cache-get',['lake','exe','cache','get'],ROOT)
    run('focal-build',['lake','build','YangMills.RG.TorusFiniteSumEnergy'],ROOT)
    olean=ROOT/'.lake/build/lib/lean/YangMills/RG/TorusFiniteSumEnergy.olean'
    if not olean.is_file(): raise RuntimeError('Missing target .olean')
    REPORT['target_olean_sha256']=hashlib.sha256(olean.read_bytes()).hexdigest()
    log=run('oracle',['lake','env','lean','YangMills/RG/TorusFiniteSumEnergyOracle.lean'],ROOT)
    content=log.read_text()
    names=['backwardShiftEnergy_eq_forward','character_forwardShiftEnergy','oneComponentStencilEnergy_eq','character_oneComponentStencilEnergy','torusCharacter_oneComponentStencilEnergy']
    matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",content)
    if len(matches)!=5: raise RuntimeError('Expected exactly five oracle reports; got '+str(len(matches)))
    checked=[]
    for (name,axs),want in zip(matches,names):
        actual_ax=[x.strip() for x in axs.split(',') if x.strip()]
        if name!='YangMills.RG.'+want or set(actual_ax)!={'propext','Classical.choice','Quot.sound'} or len(actual_ax)!=3:
            raise RuntimeError('Oracle mismatch '+repr((name,actual_ax,want)))
        checked.append({'name':name,'axioms':actual_ax})
    REPORT['oracle_reports']=checked
    REPORT['status']='FOCAL_REPRODUCTION_PASS'
except BaseException as e:
    REPORT['status']='FAIL'; REPORT['error']=str(e)
    (OUT/'exception.txt').write_text(traceback.format_exc())
    print(traceback.format_exc(),flush=True)
finally:
    REPORT['finished_utc']=datetime.now(timezone.utc).isoformat()
    (OUT/'report.json').write_text(json.dumps(REPORT,indent=2))
    checks={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in OUT.iterdir() if p.is_file()}
    (OUT/'manifest.json').write_text(json.dumps(checks,indent=2))
    bundle=pathlib.Path('/content/eriksson-paper47-evidence-016.zip')
    with zipfile.ZipFile(bundle,'w',zipfile.ZIP_DEFLATED) as z:
        for p in OUT.iterdir():
            if p.is_file(): z.write(p,p.name)
    print('FINAL_REPORT='+json.dumps(REPORT),flush=True)
    print('BUNDLE_SHA256='+hashlib.sha256(bundle.read_bytes()).hexdigest(),flush=True)
    print('The following download must be verified locally; this is one focal run, not terminal closure.',flush=True)
    import base64, html
    payload=base64.b64encode(bundle.read_bytes()).decode('ascii')
    print('EVIDENCE_BASE64_BEGIN='+payload+'=EVIDENCE_BASE64_END',flush=True)
    from IPython.display import display, HTML
    display(HTML('<a download="eriksson-paper47-evidence-016.zip" href="data:application/zip;base64,'+payload+'">Download evidence ZIP 016</a>'))
    try:
        from google.colab import runtime
        print('INLINE_EVIDENCE_EMITTED; releasing runtime.',flush=True)
        runtime.unassign()
    except BaseException as e:
        print('RUNTIME_RELEASE_ERROR='+repr(e),flush=True)

