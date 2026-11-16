"""Prospective raw-return354A validator. No assertions, no archive extraction.
Byte/record consistency only: not independent proof of execution or PDF layout.
"""
import os, io, re, json, hashlib, zipfile
from pathlib import Path, PurePosixPath
from datetime import datetime
if os.name!='posix' or not Path('/content').is_dir():
    raise RuntimeError('Own Colab Linux only; no Windows import')
BASE=Path(__file__).resolve().parent
SOURCE='8e452190b8f7d3f7382ba2e6c05d0f14fa9c3dc5'
PAPER='papers/stationary-weighting354'
BRANCH='codex/tep-weighting354-source-20261114'
ROOT='/content/tep354D-build-01'
PACKET='/content/production354D-preparation'
EPOCH='1794629658'
TEX='b8cbd2a1b1d817a6889f2219134213b0a9bdeaf20e77d006cebfedcbb59e9233'
INPUTS='cf80a4263ff21f87508ba33a2ebe17b8a4dcad3ca1018651e9ec057dc1970370'
BUILDER='b3323cb6ba8b6cccba95e7cb7a87a1e4cfecae0ea0fc854980e4c38e5e3d90e7'
LAUNCHER='0891ccf573894f3f94463af89b40b9456b402ac2f1c721bea1267db996fe9845'
PREP='a00396adb63fce545d8ab675c13865efdb5f192ac7088f859ba23f612149d459'
MARKER='968d66a7b491c7728f2ab009dcb54ac0025d6f474de6f3734f66b8809f6c18a8'
STATUS='TWO_FRESH_MATCHING_PDFS_RENDERED_PENDING_ALL_PAGE_VISUAL_AND_FIRST_EXACT_PDF_ASSESSMENT'
TEX_ARG=(r'\pdfinfoomitdate=1\pdftrailerid{}'
         r'\ifdefined\pdfsuppressptexinfo\pdfsuppressptexinfo=15\fi'
         r'\input{manuscript354.tex}')
MARKERS=('Stationary-to-weighting moment transfer and spectral rigidity','Setting and theorem map',
 'Failure of exact critical-cap transfer','Inverse moments and subcritical transfer',
 'Full-chain estimates for code-supported potentials','Disjoint blocks and a strictly larger potential class',
 'Positive-rate families at every sufficiently large length','Positioning, failed routes and remaining question',
 'Model assessments and review context')
COMMANDS=['apt-update','apt-install','tex-version','poppler-version','git-version']
for m in ('a','b'):
    COMMANDS += ['clone-'+m,'head-'+m,'sparse-init-'+m,'sparse-set-'+m,'checkout-'+m]
    if m=='a': COMMANDS += ['source-files-a']
    COMMANDS += ['epoch-'+m,'tex-'+m+'-pass1','tex-'+m+'-pass2','tracked-diff-'+m]
COMMANDS += ['pdfinfo','extract','render']
COMPILES={f'tex-{m}-pass{n}' for m in ('a','b') for n in (1,2)}
ENV={'SOURCE_DATE_EPOCH':EPOCH,'FORCE_SOURCE_DATE':'1','TZ':'UTC','LC_ALL':'C.UTF-8'}
def need(ok,msg):
    if not ok: raise ValueError(msg)
def digest(raw): return hashlib.sha256(raw).hexdigest()
def pairs(rows):
    result={}
    for k,v in rows:
        need(k not in result,'Duplicate JSON key'); result[k]=v
    return result
def js(raw): return json.loads(raw,object_pairs_hook=pairs)
def zero(raw): need(raw==b'0\n','Exact native zero sentinel')
def interval(a,b):
    x,y=datetime.fromisoformat(a),datetime.fromisoformat(b)
    need(x.tzinfo is not None and y.tzinfo is not None and y>=x,'Actual interval')
def safe_names(names):
    seen=set()
    for name in names:
        need(isinstance(name,str) and name and '\\' not in name,'Invalid path')
        need(not PurePosixPath(name).is_absolute(),'Absolute path')
        for part in name.split('/'):
            need(part not in ('','.','..') and part==part.rstrip(' .'),'Aliased path')
            need(re.search(r'[\x00-\x1f<>:"|?*]',part) is None,'Unsafe path')
            need(part.split('.')[0].upper() not in {'CON','PRN','AUX','NUL',*[f'COM{i}' for i in range(1,10)],*[f'LPT{i}' for i in range(1,10)]},'Reserved name')
        need(name.casefold() not in seen,'Duplicate/case alias');seen.add(name.casefold())
    for name in seen:
        parts=name.split('/')
        need(not any('/'.join(parts[:i]) in seen for i in range(1,len(parts))),'File/directory collision')
def unpack(raw):
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        infos=z.infolist()
        # Check raw decoded header names before ZipInfo.filename sanitization.
        original_names=[i.orig_filename for i in infos]
        safe_names(original_names)
        need(all(i.orig_filename==i.filename for i in infos),'ZIP original/sanitized name mismatch')
        names=original_names
        need(0<len(names)<5000 and sum(i.file_size for i in infos)<512_000_000,'Archive bounds')
        need(all(not i.is_dir() and (i.external_attr>>16)&0o170000 in (0,0o100000)
                 and not(i.flag_bits&1) for i in infos),'Archive must contain regular unencrypted files')
        return {i.filename:z.read(i) for i in infos}
def manifest(data,name):
    rows=js(data[name]);need(isinstance(rows,list) and rows,'Manifest rows')
    safe_names([r['path'] for r in rows])
    need({r['path'] for r in rows}==set(data)-{name},'Exact manifest membership')
    for r in rows:
        need(type(r['bytes']) is int and r['bytes']>=0 and re.fullmatch('[0-9a-f]{64}',r['sha256']) is not None,'Manifest types')
        raw=data[r['path']];need(len(raw)==r['bytes'] and digest(raw)==r['sha256'],'Manifest bytes')
def expected_command(name):
    fixed={
     'apt-update':['apt-get','-qq','update'],
     'apt-install':['apt-get','install','-y','-qq','texlive-latex-base','texlive-latex-recommended','lmodern','poppler-utils','python3-pil'],
     'tex-version':['pdflatex','--version'], 'poppler-version':['pdftoppm','-v'], 'git-version':['git','--version'],
     'source-files-a':['git','ls-files','--',PAPER],
     'pdfinfo':['pdfinfo',ROOT+'/evidence/manuscript354.pdf'],
     'extract':['pdftotext','-layout',ROOT+'/evidence/manuscript354.pdf',ROOT+'/evidence/manuscript354.txt'],
     'render':['pdftoppm','-r','110','-png',ROOT+'/evidence/manuscript354.pdf',ROOT+'/evidence/page']}
    if name in fixed:
        return fixed[name],ROOT+'/clone-a' if name=='source-files-a' else ROOT,{}
    if name in COMPILES:
        m=name.split('-')[1]
        return ['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error','-jobname=production354',TEX_ARG],ROOT+'/clone-'+m+'/'+PAPER,ENV
    prefix,m=name.rsplit('-',1);clone=ROOT+'/clone-'+m
    argv={
     'clone':['git','clone','--filter=blob:none','--depth','1','--no-checkout','--branch',BRANCH,'https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git',clone],
     'head':['git','rev-parse','HEAD'], 'sparse-init':['git','sparse-checkout','init','--cone'],
     'sparse-set':['git','sparse-checkout','set',PAPER], 'checkout':['git','checkout','--detach',SOURCE],
     'epoch':['git','show','-s','--format=%ct',SOURCE], 'tracked-diff':['git','diff','--exit-code',SOURCE,'--',PAPER]}[prefix]
    return argv,ROOT if prefix=='clone' else clone,{}
def native(c):
    need(type(c['actual_exit']) is int and c['actual_exit']==0 and c['timed_out'] is False,'Actual command failure')
    argv,cwd,env=expected_command(c['name'])
    need(c['argv']==argv and c['cwd']==cwd and c['environment_controls']==env,'Exact native command contract')
    interval(c['started_at'],c['finished_at'])
def owner(o):
    need(o['own_runtime'] is True and o['runtime_kind']=='CPU' and bool(o['session_reference']) and bool(o['observed_at']),'Own runtime observation')
def child(c,kind):
    need(type(c['actual_exit']) is int and c['actual_exit']==0,'Actual child exit')
    interval(c['started_at'],c['finished_at'])
    a=c['argv']
    if kind=='marker': need(a==['node',PACKET+'/mark_artifact_operation_started.mjs','--operation-kind','create','--expected-output-count','1','--output-format','pdf'],'Exact marker argv')
    else: need(isinstance(a,list) and len(a)==2 and isinstance(a[0],str) and a[0].startswith('/') and a[1]==PACKET+'/build354D.py','Exact builder argv')
def validate_bytes(raw):
    need(type(raw) is bytes and 0<len(raw)<512_000_000,'Bounded raw return bytes')
    outer=unpack(raw)
    outer_names={'RETURN-MANIFEST.json','launch-receipt354D.json','launch-result354D.json',
     'marker354D.stdout','marker354D.stderr','marker354D.exit','builder354D.stdout','builder354D.stderr',
     'builder354D.exit','tep354D-build-01-results.zip'}
    need(set(outer)==outer_names,'Exact outer result membership');manifest(outer,'RETURN-MANIFEST.json')
    for n in ('marker354D.exit','builder354D.exit'): zero(outer[n])
    launch=js(outer['launch-receipt354D.json']);result=js(outer['launch-result354D.json'])
    need(launch['source']==result['source']==SOURCE and launch['builder_sha256']==BUILDER and launch['launcher_sha256']==LAUNCHER,'Launch identity')
    need(type(launch['marker_actual_exit']) is int and launch['marker_actual_exit']==0,'Marker native exit')
    child(launch['marker'],'marker'); child(result['builder'],'builder'); owner(launch['owner_observation'])
    need(result['owned_runtime_closed'] is False and result['billing_units'] is None and result['exact_pdf_review'] is None,'No fabricated closure/billing/review')
    interval(launch['marker']['finished_at'],result['builder']['started_at'])
    interval(result['builder']['finished_at'],result['finished_at'])
    announcements=[]
    for line in outer['builder354D.stdout'].decode('utf-8').splitlines():
        if line.startswith('{'):
            val=js(line)
            if 'archive_sha256' in val: announcements.append(val)
    need(len(announcements)==1,'Single actual builder announcement');ann=announcements[0]
    innerraw=outer['tep354D-build-01-results.zip']
    need(ann['status']==STATUS and ann['archive']==ROOT+'-results.zip' and type(ann['archive_bytes']) is int
         and ann['archive_bytes']==len(innerraw) and ann['archive_sha256']==digest(innerraw),'Actual inner archive announcement')
    data=unpack(innerraw);manifest(data,'evidence/manifest.json')
    def get(name): return data['evidence/'+name]
    r=js(get('report.json'))
    need(r['source']==SOURCE and r['tex_raw_sha256']==TEX and r['input_manifest_sha256']==INPUTS
         and r['status']==STATUS and r['tex_argument']==TEX_ARG and r['source_epoch']==EPOCH,'Report subject/status')
    need(r['math_tests'] is False and r['formal_verification'] is False and r['new_assessment'] is None
         and r['billing_units'] is None and r['billing_seconds'] is None
         and r['release_status']=='OWNED_SESSION_CLOSURE_MUST_BE_OBSERVED_AFTER_RETURN','Scope/resource integrity')
    need(r['runtime_owner_claim']==launch['owner_observation'] and bool(r['hostname']) and bool(r['platform']),'Actual runtime binding')
    interval(r['started_at'],r['finished_at'])
    need(type(r['observed_builder_wall_seconds']) in (int,float) and r['observed_builder_wall_seconds']>=0,'Observed wall time')
    need(type(r['pages']) is int and 1<=r['pages']<=60,'Actual page count')
    builds=r['builds'];need(len(builds)==2 and [b['mode'] for b in builds]==['a','b'],'Two fresh builds')
    for b in builds:
        need(b['source']==SOURCE and b['epoch']==EPOCH and type(b['input_files_verified']) is int
             and b['input_files_verified']==85 and type(b['pdf_bytes']) is int and b['pdf_bytes']>0,'Build record')
    need(all(builds[0][k]==builds[1][k] for k in ('pdf_sha256','pdf_bytes','epoch')),'Build difference')
    need([c['name'] for c in r['commands']]==COMMANDS,'Exact native command sequence')
    for c in r['commands']:
        native(c); zero(get(c['name']+'.exit'))
        get(c['name']+'.stdout');get(c['name']+'.stderr')
    need(r['cleanup']==[{'path':ROOT+'/clone-'+m,'removed':True} for m in ('a','b')],'Cleanup debt')
    frozen=(BASE/'frozen-producer'/'SOURCE-INPUTS354D.json').read_bytes()
    need(digest(frozen)==INPUTS,'Validator frozen inventory changed');rows=js(frozen)['entries']
    need(len(rows)==85,'85 source inputs');safe_names([x['path'] for x in rows])
    captured={n[len('evidence/source-capture/'):] for n in data if n.startswith('evidence/source-capture/')}
    need(captured=={x['path'] for x in rows},'Exact source capture membership')
    for x in rows:
        b=get('source-capture/'+x['path'])
        blob=hashlib.sha1(b'blob '+str(len(b)).encode('ascii')+b'\0'+b).hexdigest()
        need(len(b)==x['bytes'] and digest(b)==x['sha256'] and blob==x['git_blob_sha1'],'Source raw/blob binding')
    need(digest(get('source-capture/manuscript354.tex'))==TEX,'Active TeX')
    for m in ('a','b'):
        need(get('head-'+m+'.stdout').decode().strip()==SOURCE and get('epoch-'+m+'.stdout').decode().strip()==EPOCH,'Actual clone head/epoch')
        need(not get('tracked-diff-'+m+'.stdout').strip(),'Tracked modification')
    need(set(get('source-files-a.stdout').decode().splitlines())=={PAPER+'/'+x['path'] for x in rows},'Actual git file universe')
    pdf=get('manuscript354.pdf');need(pdf.startswith(b'%PDF-') and len(pdf)==builds[0]['pdf_bytes'] and digest(pdf)==builds[0]['pdf_sha256'],'Canonical PDF')
    for m in ('a','b'): need(get('clone-'+m+'.pdf')==pdf,'Actual clone PDF mismatch')
    info=get('pdfinfo.stdout').decode();match=re.search(r'(?m)^Pages:\s+(\d+)\s*$',info)
    need(match is not None and int(match.group(1))==r['pages'] and r['pdfinfo']==info,'Actual pdfinfo')
    pages={n for n in data if re.fullmatch(r'evidence/page-[0-9]+\.png',n)}
    need(len(pages)==r['pages'] and {int(n.split('-')[-1].split('.')[0]) for n in pages}==set(range(1,r['pages']+1)),'All page indices')
    contacts={n for n in data if re.fullmatch(r'evidence/contact-[0-9]+\.jpg',n)}
    need(contacts=={f'evidence/contact-{i:02d}.jpg' for i in range(1,(r['pages']+3)//4+1)},'All contact sheets')
    need(all(data[n].startswith(b'\x89PNG\r\n\x1a\n') for n in pages),'PNG signature')
    need(all(data[n].startswith(b'\xff\xd8\xff') and data[n].endswith(b'\xff\xd9') for n in contacts),'JPEG signature')
    extracted=get('manuscript354.txt').decode();normal=' '.join(extracted.split())
    need(all(m in normal for m in MARKERS) and '??' not in extracted and '[SLOT]' not in extracted,'Exact content guards')
    binding=js(get('source-binding354.json'))
    need(binding['source']==SOURCE and binding['paper']==PAPER and binding['active_tex_sha256']==TEX
         and binding['input_manifest_sha256']==INPUTS and binding['pdf_sha256']==digest(pdf)
         and binding['tex_argument']==TEX_ARG and binding['input_files']==rows,'Source/PDF full binding')
    universe={'evidence/'+n for n in ('report.json','manifest.json','source-binding354.json','manuscript354.pdf','manuscript354.txt','clone-a.pdf','clone-b.pdf','clone-a-latex.log','clone-b-latex.log')}
    universe |= {'evidence/'+n+ext for n in COMMANDS for ext in ('.stdout','.stderr','.exit')}
    universe |= {'evidence/source-capture/'+n for n in captured}|pages|contacts
    for m in ('a','b'):
        previous=None
        for passno in (1,2):
            name=f'tex-{m}-pass{passno}';prefix='native-tex/'+name+'/'
            rt=js(get(prefix+'retention.json')); saved=rt['files_saved_after_attempt']
            need(rt['attempt']==name and rt['actual_child_result']==next(c for c in r['commands'] if c['name']==name),'Native child retention')
            safe_names([x['path'] for x in saved])
            need({x['path'] for x in saved}=={'manuscript354.tex'}|{'production354'+e for e in ('.pdf','.log','.aux','.out')},'Native retained membership')
            for x in saved:
                b=get(prefix+x['path']);need(len(b)==x['bytes'] and digest(b)==x['sha256'],'Native bytes')
            need(digest(get(prefix+'manuscript354.tex'))==TEX,'Native source')
            expected_prior={'manuscript354.tex':{'bytes':len(get('source-capture/manuscript354.tex')),'sha256':TEX}} if passno==1 else previous
            need(rt['files_before_attempt']==expected_prior,'Native prior-output lineage')
            previous={x['path']:{'bytes':x['bytes'],'sha256':x['sha256']} for x in saved}
            if passno==2:
                need(get(prefix+'production354.pdf')==pdf,'Final native PDF')
                log=get(prefix+'production354.log');need(log==get('clone-'+m+'-latex.log'),'Final native log')
                need(b'There were undefined references' not in log and b'Citation `' not in log,'Unresolved final references')
                need(builds[0 if m=='a' else 1]['overfull_lines']==[s for s in log.decode(errors='replace').splitlines() if 'Overfull' in s],'Overfull warning retention')
            universe|={'evidence/'+prefix+x['path'] for x in saved}|{'evidence/'+prefix+'retention.json'}
    pp='production-preparation/'
    static_names=('build354D.py','launch354D.py','SOURCE-INPUTS354D.json','PREPARATION-MANIFEST.json','mark_artifact_operation_started.mjs','README.txt')
    for n in static_names:
        local=(BASE/'frozen-producer'/n).read_bytes();need(get(pp+n)==local,'Frozen producer byte identity')
    need(digest(get(pp+'build354D.py'))==BUILDER and digest(get(pp+'launch354D.py'))==LAUNCHER
         and digest(get(pp+'PREPARATION-MANIFEST.json'))==PREP and digest(get(pp+'mark_artifact_operation_started.mjs'))==MARKER,'Pinned producer identity')
    dynamic=('launch-receipt354D.json','marker354D.stdout','marker354D.stderr','marker354D.exit')
    for n in dynamic: need(get(pp+n)==outer[n],'Outer/inner launch binding')
    gate=js(get(pp+'gates/authorization.json'))
    need(digest(get(pp+'gates/authorization.json'))==launch['gate_sha256'] and gate['source']==SOURCE
         and gate['status']=='READY_AFTER_ACTUAL_PARENT_REVIEW' and gate['reviewed_builder_sha256']==BUILDER
         and gate['reviewed_launcher_sha256']==LAUNCHER and gate['owner_observation']==launch['owner_observation'],'Gate identity')
    gate_names=['authorization.json']
    for key in ('source_integration_review','production_engineering_review','required_ci'):
        row=gate[key];safe_names([row['path']]);gate_names.append(row['path'])
        need(row['source']==SOURCE and row['status']=='ACCEPTED' and digest(get(pp+'gates/'+row['path']))==row['sha256'],'Raw gate receipt binding')
    safe_names(gate_names)
    universe|={'evidence/'+pp+n for n in static_names+dynamic}
    # This validator accepts exactly the three named raw gate receipts plus
    # authorization.json. A complete multi-file report can be one bound ZIP receipt.
    all_gates={n[len('evidence/'+pp+'gates/'):] for n in data if n.startswith('evidence/'+pp+'gates/')}
    need(all_gates==set(gate_names),'Exact gates membership; no unbound extras')
    universe|={'evidence/'+pp+'gates/'+n for n in gate_names}
    need(set(data)==universe,'Exact inner membership')
    return dict(source=SOURCE,pdf_sha256=digest(pdf),pdf_bytes=len(pdf),pages=r['pages'],
                return_sha256=digest(raw),inner_sha256=digest(innerraw),source_files_verified=85,
                inner_members_verified=len(data),native_commands_verified=len(COMMANDS),
                scope='Raw consistency, memberships, source identities, declared commands and actual recorded exits. Not independent execution attestation, PDF decoding/layout, mathematical review or session closure.')
def validate_file(path,expected_bytes,expected_sha):
    need(path.is_file() and not path.is_symlink(),'Regular input archive')
    need(type(expected_bytes) is int and 0<expected_bytes<512_000_000 and path.stat().st_size==expected_bytes,'Input size before read')
    raw=path.read_bytes()
    need(type(expected_bytes) is int and expected_bytes>0 and len(raw)==expected_bytes
         and re.fullmatch('[0-9a-f]{64}',expected_sha) is not None and digest(raw)==expected_sha,'Actual transport binding')
    return validate_bytes(raw)
