"""UNAUTHORIZED PROPOSAL. GitHub Linux file validation only; never Colab provenance."""
import os,sys,json,hashlib,subprocess,signal,time,platform,traceback,zipfile,re
from pathlib import Path
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent
BASE=HERE/'inputs'/'return-validation354C'
OUT=HERE/'receipts354-github'
SOURCE='8e452190b8f7d3f7382ba2e6c05d0f14fa9c3dc5'
C_MANIFEST='c2176b80b34438fbd970cb0d6df41fb2c1c9b20d3b03946c9fee31fe4155243f'
def require(ok,message):
    if not ok:raise RuntimeError(message)
def digest(raw):return hashlib.sha256(raw).hexdigest()
def regular(path):
    require(path.is_file() and not path.is_symlink(),'Actual regular file: '+str(path))
    return path.read_bytes()
def authorization():
    require(os.name=='posix' and platform.system()=='Linux','Linux only')
    require(os.environ.get('GITHUB_ACTIONS')=='true','Actual GitHub context')
    require(os.environ.get('GITHUB_REPOSITORY')=='lluiseriksson/THE-ERIKSSON-PROGRAMME','Exact repository')
    for key in ('GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT'):
        require(re.fullmatch('[1-9][0-9]*',os.environ.get(key,'')) is not None,'Actual '+key)
    require(re.fullmatch('[0-9a-f]{40}',os.environ.get('GITHUB_SHA','')) is not None,'Actual commit')
    require(os.environ.get('GITHUB_EVENT_NAME')=='workflow_dispatch','Manual dispatch only')
    authraw=regular(HERE/'authorization'/'AUTHORIZATION.approved.json');auth=json.loads(authraw)
    require(auth['authorized'] is True and auth['scope']=='github-linux-file-validation354-only','Explicit owner exception absent')
    require(auth['compatibility_content_directory_authorized'] is True,'Explicit /content compatibility exception')
    require(auth['existing_quota_confirmed'] is True and auth['additional_spend_authorized'] is False,'Existing quota only')
    require(auth['approved_workflow_commit']==os.environ['GITHUB_SHA'],'Exact dispatched commit')
    require(isinstance(auth['owner_instruction_reference'],str) and bool(auth['owner_instruction_reference'].strip()),'Real instruction reference')
    instruction=regular(HERE/'authorization'/'owner-instruction.raw')
    require(len(instruction)>0 and digest(instruction)==auth['owner_instruction_sha256'],'Real instruction bytes')
    review=regular(HERE/'authorization'/'independent-review.raw')
    require(len(review)>0 and digest(review)==auth['independent_review_sha256'] and auth['independent_review_accepted'] is True,'Separate exact review')
    manifest=regular(HERE/'PROPOSAL-MANIFEST.json')
    require(digest(manifest)==auth['proposal_manifest_sha256'],'Approved exact proposal')
    rows=json.loads(manifest)['payloads'];seen=set()
    for row in rows:
        name=row['path'];require(isinstance(name,str) and name and '/' not in name and '\\' not in name and name not in ('.','..') and name not in seen,'Safe unique proposal name');seen.add(name)
        raw=regular(HERE/name)
        require(len(raw)==row['bytes'] and digest(raw)==row['sha256'],'Approved proposal bytes')
    require({'github_validate354.py','validation354-proposal.yml'}.issubset(seen),'Adapter/workflow pins')
    deployed=regular(Path(os.environ['GITHUB_WORKSPACE'])/'.github'/'workflows'/'validation354-proposal.yml')
    require(deployed==regular(HERE/'validation354-proposal.yml'),'Exact reviewed deployed workflow')
    return auth,authraw,instruction,review
AUTH,AUTHRAW,INSTRUCTION,REVIEW=authorization()
if len(sys.argv)==2 and sys.argv[1]=='--authorize-only':
    print(json.dumps(dict(status='EXACT_EXCEPTION_AND_REVIEW_BOUND',backend='GitHub Actions Linux',colab=False)))
    raise SystemExit(0)
require(len(sys.argv)==1,'No unrecognized options')
require(Path('/content').is_dir() and not Path('/content').is_symlink(),'Explicit compatibility directory required')
require(not OUT.exists() and not OUT.is_symlink(),'Fresh receipts')
OUT.mkdir()
sys.path.insert(0,str(BASE))
import atomic354A as a
import validate354A as v
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
status='FAILED_PRESERVED';summaries={}
source_path=HERE/'inputs'/'tep354D-return.zip'
config=dict(source=SOURCE,bytes=7002490,sha256='d079cfee6714aee9c239a2d41546e0beea832dab2421627f2f759d06e0d2049e')
try:
    v.need(v.digest(regular(BASE/'MANIFEST354A.json'))==C_MANIFEST,'Exact C manifest')
    verify_payloads()
    v.need(type(config['bytes']) is int and 0<config['bytes']<512_000_000 and source_path.is_file()
           and not source_path.is_symlink() and source_path.stat().st_size==config['bytes'],'Original input size before read')
    actual=regular(source_path);v.need(len(actual)==config['bytes'] and v.digest(actual)==config['sha256'],'Original return transport identity')
    closure=regular(HERE/'inputs'/'production354D-runtime-closure.json')
    v.need(v.digest(closure)=='19898545e3be4a3c5cb715b6f195337e57f8fc35cbec1bd61a438216e947e6c8','Actual historical production closure bytes')
    put(OUT/'input-observation.json',dict(**config,backend='GitHub Actions Linux',colab=False,
        compatibility_directory_only='/content',github={key:os.environ.get(key) for key in
        ('GITHUB_REPOSITORY','GITHUB_SHA','GITHUB_WORKFLOW_REF','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_ACTOR','GITHUB_EVENT_NAME','RUNNER_OS','RUNNER_ARCH','RUNNER_NAME')},
        hostname=platform.node(),platform=platform.platform(),python=sys.version,observed_at=now(),
        production_closure_sha256=digest(closure),prior_production_closure_not_a_new_observation=True))
    for name,raw in [('owner-instruction.raw',INSTRUCTION),('independent-review.raw',REVIEW),
                     ('AUTHORIZATION.approved.json',AUTHRAW),('production-closure-evidence',closure)]:
        with (OUT/name).open('xb') as f:f.write(raw)
except BaseException:
    (OUT/'prerequisite-failure.txt').write_text(traceback.format_exc(),encoding='utf-8')
    raise
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
          'outer-raw-manifest-hash','duplicate-ZIP-members','symlink-ZIP-member',
          'raw-NUL-outer-local-and-central','raw-NUL-inner-local-and-central-rebound',
          'announcement-compact-producer-protocol-positive',
          'announcement-original-B-pretty-JSONDecodeError-preserved',
          'announcement-duplicate-rejected','announcement-absent-rejected'}
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
        hostname=platform.node(),backend='GitHub Actions Linux',colab=False,billing_units=None,
        runner_job_finished_observed=False,no_pdf_authored=True,
        closure='Parent must observe final GitHub job status; no Colab closure or terminal reproduction claimed'))
    (OUT/'validator-manifest.json').write_bytes((BASE/'MANIFEST354A.json').read_bytes())
    rows=[dict(path=p.name,bytes=p.stat().st_size,sha256=v.digest(p.read_bytes())) for p in sorted(OUT.iterdir()) if p.is_file()]
    put(OUT/'receipts-manifest.json',rows)
    archive=HERE/'validation354-github-receipts.zip'
    with zipfile.ZipFile(archive,'x',zipfile.ZIP_DEFLATED) as z:
        for p in sorted(OUT.iterdir()):
            if p.is_file():z.write(p,p.name)
    print(json.dumps(dict(status=status,path=str(archive),bytes=archive.stat().st_size,sha256=v.digest(archive.read_bytes()),backend='GitHub Actions Linux',colab=False)))
if status=='FAILED_PRESERVED':raise RuntimeError('Validation failed; keep all evidence, no blind rerun')
