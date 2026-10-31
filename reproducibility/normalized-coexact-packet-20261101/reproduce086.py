import os, sys, json, re, time, hashlib, subprocess, pathlib, zipfile, traceback, urllib.request
from datetime import datetime, timezone
SHA='efce8500b058af4a46dccac4f9dec94634b20f17'
EXPECTED=json.loads(r'''{"NormalizedCoexactPacketOracle.lean":"6b6a1982f31c389e7bdbef066fccf8c09a313fd69210f550f5d076d218eef236","NormalizedCoexactPacket.lean":"6d9ddf1268a471274af40332dd57f2cb4a6a23839f40059f202d520856d531d7"}''')
ROOT=pathlib.Path('/content/eriksson-normalized-coexact-packet-20261101-086')
OUT=pathlib.Path('/content/eriksson-normalized-coexact-packet-evidence-086')
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
    if len(mathlib)!=1 or mathlib[0]['rev']!='07642720480157414db592fa85b626dafb71355b': raise RuntimeError('Mathlib pin mismatch')
    run('lean-version',['lean','--version'],ROOT,600)
    run('cache-get',['lake','exe','cache','get'],ROOT)
    run('focal-build',['lake','build','YangMills.RG.NormalizedCoexactPacket'],ROOT)
    olean=ROOT/'.lake/build/lib/lean/YangMills/RG/NormalizedCoexactPacket.olean'
    if not olean.is_file(): raise RuntimeError('Missing target .olean')
    REPORT['target_olean_sha256']=hashlib.sha256(olean.read_bytes()).hexdigest()
    log=run('oracle',['lake','env','lean','YangMills/RG/NormalizedCoexactPacketOracle.lean'],ROOT)
    content=log.read_text()
    checker_source=r'''import json, re, sys, pathlib
NAMES=['counting_backward_mass_eq_forward','coexact_characterSynthesis_norm_sq','positiveCoexactCharacter_injective','positiveCoexactSymbolMass_pos','positiveCoexactNormalization_pos','normalizedCoexactSynthesis_norm_sq','normalizedCoexactSynthesis_div_zero']
PATTERN=r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def verify(content):
    matches=re.findall(PATTERN,content)
    if len(matches)!=7: raise ValueError('Wrong oracle count')
    checked=[]
    for (name,axs),want in zip(matches,NAMES):
        actual_ax=[x.strip() for x in axs.split(',') if x.strip()]
        if name!='YangMills.RG.'+want: raise ValueError('Wrong oracle name')
        if not set(actual_ax).issubset({'propext','Classical.choice','Quot.sound'}): raise ValueError('Unapproved axiom')
        if len(actual_ax)!=len(set(actual_ax)): raise ValueError('Repeated axiom')
        checked.append({'name':name,'axioms':actual_ax})
    return checked
if __name__=='__main__':
    raw=pathlib.Path(sys.argv[1]).read_text()
    verify(raw)
    hits=list(re.finditer(PATTERN,raw))
    mutations=[raw.replace(hits[0].group(1),hits[-1].group(1),1),
               raw[:hits[-1].start()]+raw[hits[-1].end():],
               raw.replace('propext','sorryAx',1)]
    rejected=0
    for bad in mutations:
        if bad==raw: raise RuntimeError('Mutation did not change real evidence')
        try: verify(bad)
        except ValueError: rejected+=1
        else: raise RuntimeError('Mutated evidence accepted')
    if rejected!=3: raise RuntimeError('Wrong rejection count')
    print(json.dumps({'status':'ORACLE_VALIDATOR_SELFTEST_PASS','real_mutations_rejected':rejected,'positive_accepted':1,'optimized':not __debug__}))
'''
    checker=ROOT/'_oracle_validator.py'
    checker.write_text(checker_source)
    selftests=[]
    for mode,flags in [('normal',[]),('optimized',['-O'])]:
        proc=subprocess.run([sys.executable]+flags+[str(checker),str(log)],capture_output=True,text=True)
        if proc.returncode!=0: raise RuntimeError('Validator selftest failed: '+mode+' '+proc.stdout+proc.stderr)
        row=json.loads(proc.stdout)
        if row['status']!='ORACLE_VALIDATOR_SELFTEST_PASS' or row['real_mutations_rejected']!=3 or row['positive_accepted']!=1 or row['optimized']!=(mode=='optimized'):
            raise RuntimeError('Wrong selftest verdict')
        selftests.append(dict(row,mode=mode))
    REPORT['oracle_validator_selftests']=selftests
    namespace={'__name__':'validator_import'}
    exec(checker_source,namespace)
    checked=namespace['verify'](content)
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
    bundle=pathlib.Path('/content/eriksson-normalized-coexact-packet-evidence-086.zip')
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
    display(HTML('<a download="eriksson-normalized-coexact-packet-evidence-086.zip" href="data:application/zip;base64,'+payload+'">Download evidence ZIP 086</a>'))
    try:
        from google.colab import runtime
        print('INLINE_EVIDENCE_EMITTED; releasing runtime.',flush=True)
        runtime.unassign()
    except BaseException as e:
        print('RUNTIME_RELEASE_ERROR='+repr(e),flush=True)
