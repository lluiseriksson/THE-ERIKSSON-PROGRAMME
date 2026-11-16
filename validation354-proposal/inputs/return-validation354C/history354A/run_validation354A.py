"""Prospective actual354A run: owned Linux session, meaningful normal/-O guards."""
import os,sys,json,hashlib,subprocess,signal,time,platform,traceback,zipfile
from pathlib import Path
from datetime import datetime,timezone
import atomic354A as a
import validate354A as v
BASE=Path(__file__).resolve().parent
OUT=BASE/'actual-receipts354A'
def put(path,value):
    with path.open('xb') as f:f.write((json.dumps(value,indent=2)+'\n').encode())
def now():return datetime.now(timezone.utc).isoformat()
def verify_payloads():
    rows=json.loads((BASE/'MANIFEST354A.json').read_bytes())['payloads'];v.safe_names([x['path'] for x in rows])
    for row in rows:
        path=BASE/row['path'];v.need(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(BASE),'Frozen validation payload')
        raw=path.read_bytes();v.need(len(raw)==row['bytes'] and v.digest(raw)==row['sha256'],'Frozen validation hash')
def observed(name,argv,timeout):
    prefix=OUT/name;obs=dict(argv=argv,hostname=platform.node(),started_at=now(),actual_exit=None,timed_out=False,error=None)
    child=None;start=time.monotonic()
    try:
        with prefix.with_suffix('.stdout').open('xb') as out,prefix.with_suffix('.stderr').open('xb') as err:
            child=subprocess.Popen(argv,cwd=BASE,stdout=out,stderr=err,start_new_session=True)
            try:obs['actual_exit']=child.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                obs['timed_out']=True
                try:os.killpg(child.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                obs['actual_exit']=child.wait()
            out.flush();os.fsync(out.fileno());err.flush();os.fsync(err.fileno())
    except BaseException:
        obs['error']=traceback.format_exc()
        if child is not None and child.poll() is None:
            try:os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            obs['actual_exit']=child.wait()
        raise
    finally:
        obs.update(finished_at=now(),wall_seconds=time.monotonic()-start)
        if obs['actual_exit'] is not None:a.publish_exit(prefix,obs['actual_exit'])
        obs['files']={ext:dict(bytes=prefix.with_suffix(ext).stat().st_size,sha256=v.digest(prefix.with_suffix(ext).read_bytes()))
                      for ext in ('.stdout','.stderr','.exit') if prefix.with_suffix(ext).is_file()}
        put(prefix.with_suffix('.observation.json'),obs)
    a.read_exit(prefix.with_suffix('.exit'),True)
    v.need(obs['actual_exit']==0 and not obs['timed_out'] and obs['error'] is None,'Actual native child failed')
    return json.loads(prefix.with_suffix('.stdout').read_bytes())
verify_payloads()
v.need(not OUT.exists() and not OUT.is_symlink(),'Fresh validation attempt')
config=json.loads((BASE/'ACTUAL-INPUT.json').read_bytes())
v.need(config['source']==v.SOURCE and config['status']=='ACTUAL_INPUT_AND_OWN_RUNTIME_OBSERVED','Real input observation required')
v.need(config['validation_own_runtime'] is True and config['validation_hostname']==platform.node()
       and bool(config['validation_session_reference']) and bool(config['observed_at']),'Actual owned validation host')
v.need(config['production_runtime_closed'] is True and bool(config['production_closure_evidence']),'Production closure evidence prerequisite')
closure=BASE/config['production_closure_evidence'];v.safe_names([config['production_closure_evidence']])
v.need(closure.is_file() and not closure.is_symlink() and closure.resolve().is_relative_to(BASE)
       and v.digest(closure.read_bytes())==config['production_closure_sha256'],'Actual closure receipt bytes')
source_path=BASE/'tep354D-return.zip'
v.need(source_path.is_file() and not source_path.is_symlink(),'Materialize exact return first')
v.need(type(config['bytes']) is int and 0<config['bytes']<512_000_000 and source_path.stat().st_size==config['bytes'],'Input size before read')
actual=source_path.read_bytes();v.need(len(actual)==config['bytes'] and v.digest(actual)==config['sha256'],'Original return transport identity')
OUT.mkdir();put(OUT/'input-observation.json',config)
(OUT/'production-closure-evidence').write_bytes(closure.read_bytes())
status='FAILED_PRESERVED';summaries={}
try:
    for name,args in (('normal',[]),('optimized',['-O'])):
        result=observed('preflight-'+name,[sys.executable,*args,str(BASE/'preflight354A.py')],300)
        v.need(result['status']=='SYNTHETIC_GUARDS_PASSED' and result['fixture_not_actual_pdf'] is True
               and result['count']==len(result['scenarios']) and len(set(result['scenarios']))==result['count'],'Real guard result')
        mandatory={'positive-full-synthetic-record-including-tex-version-and-four-compiles',
          'tex-version-is-not-compile','compile-is-not-version','compile-shell-escape',
          'native-sentinel-nonzero','native-sentinel-empty','native-sentinel-malformed','native-sentinel-absent',
          'native-bool-field','native-timeout','source-raw-mutation','native-prior-lineage',
          'producer-script','gate-pending-after-rebinding','atomic-native-zero','atomic-native-nonzero',
          'reader-rejects-unpublished-exit','atomic-noreplace-race','transport-hash-before-write',
          'outer-raw-manifest-hash','duplicate-ZIP-members','symlink-ZIP-member'}
        v.need(result['count']>=60 and mandatory.issubset(set(result['scenarios'])),'Meaningful current guards missing')
        v.need(result['optimized']==bool(args),'Actual normal/-O mode')
        summaries['preflight-'+name]=result
    v.need(summaries['preflight-normal']['scenarios']==summaries['preflight-optimized']['scenarios'],'Normal/-O guard scenarios differ')
    for name,args in (('normal',[]),('optimized',['-O'])):
        summaries['actual-'+name]=observed('actual-'+name,[sys.executable,*args,str(BASE/'actual354A.py'),str(source_path),str(config['bytes']),config['sha256']],600)
    v.need(summaries['actual-normal']==summaries['actual-optimized'],'Normal/-O actual results differ')
    status='RAW_RETURN_VALIDATED_PENDING_VISUAL_AND_EXACT_PDF_ASSESSMENT'
except BaseException:
    (OUT/'failure.txt').write_text(traceback.format_exc(),encoding='utf-8')
finally:
    put(OUT/'validation-summary.json',dict(source=v.SOURCE,status=status,results=summaries,finished_at=now(),
        hostname=platform.node(),billing_units=None,owned_validation_runtime_closed=False,
        closure='Parent must close this owned session after byte return and observe absence',no_pdf_authored=True))
    (OUT/'validator-manifest.json').write_bytes((BASE/'MANIFEST354A.json').read_bytes())
    rows=[dict(path=p.name,bytes=p.stat().st_size,sha256=v.digest(p.read_bytes())) for p in sorted(OUT.iterdir()) if p.is_file()]
    put(OUT/'receipts-manifest.json',rows)
    archive=BASE/'validation354A-receipts.zip'
    with zipfile.ZipFile(archive,'x',zipfile.ZIP_DEFLATED) as z:
        for p in sorted(OUT.iterdir()):
            if p.is_file():z.write(p,p.name)
    print(json.dumps(dict(status=status,path=str(archive),bytes=archive.stat().st_size,sha256=v.digest(archive.read_bytes()))))
if status=='FAILED_PRESERVED':raise RuntimeError('Validation failed; keep all evidence, no blind rerun')
