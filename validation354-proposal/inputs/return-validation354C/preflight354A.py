"""Synthetic record-mutation preflight; no fake claim of actual PDF production."""
import copy,io,json,zipfile,tempfile,hashlib
from pathlib import Path
import validate354A as v
import atomic354A as a
STAMP='2026-11-14T00:00:00+00:00'
def dump(x):return (json.dumps(x,indent=2)+'\n').encode()
# Builder stdout is a single JSON line, unlike pretty-printed record files.
def announcement_dump(x):return (json.dumps(x)+'\n').encode()
def zip_bytes(data):
    out=io.BytesIO()
    with zipfile.ZipFile(out,'w',zipfile.ZIP_DEFLATED) as z:
        for n,b in data.items():z.writestr(n,b)
    return out.getvalue()
def stamp_manifest(data,name):
    data[name]=dump([dict(path=n,bytes=len(b),sha256=v.digest(b)) for n,b in data.items() if n!=name])
def fixture():
    data={};put=lambda n,b:data.__setitem__('evidence/'+n,b)
    rows=v.js((v.BASE/'frozen-producer'/'SOURCE-INPUTS354D.json').read_bytes())['entries']
    for row in rows:
        put('source-capture/'+row['path'],(v.BASE/'source-snapshot'/v.PAPER/row['path']).read_bytes())
    # Not a decodable PDF or rendered image. Deliberate structural fixture only.
    pdf=b'%PDF-SYNTHETIC-STRUCTURAL-FIXTURE\n';log=b'SYNTHETIC successful final TeX log\n'
    for n in ('manuscript354.pdf','clone-a.pdf','clone-b.pdf'):put(n,pdf)
    put('manuscript354.txt','\n'.join(v.MARKERS).encode())
    put('page-1.png',b'\x89PNG\r\n\x1a\nSYNTHETIC')
    put('contact-01.jpg',b'\xff\xd8\xffSYNTHETIC\xff\xd9')
    cmds=[]
    for name in v.COMMANDS:
        argv,cwd,env=v.expected_command(name)
        cmds.append(dict(name=name,argv=argv,cwd=cwd,environment_controls=env,actual_exit=0,timed_out=False,started_at=STAMP,finished_at=STAMP))
        put(name+'.exit',b'0\n');put(name+'.stdout',b'');put(name+'.stderr',b'')
    for m in ('a','b'):
        put('head-'+m+'.stdout',(v.SOURCE+'\n').encode());put('epoch-'+m+'.stdout',(v.EPOCH+'\n').encode())
        put('clone-'+m+'-latex.log',log)
        prior={'manuscript354.tex':{'bytes':len(data['evidence/source-capture/manuscript354.tex']),'sha256':v.TEX}}
        for n in (1,2):
            name=f'tex-{m}-pass{n}';pre='native-tex/'+name+'/'
            files={'manuscript354.tex':data['evidence/source-capture/manuscript354.tex'],
                   'production354.pdf':pdf,'production354.log':log,'production354.aux':b'', 'production354.out':b''}
            saved=[dict(path=x,bytes=len(b),sha256=v.digest(b)) for x,b in files.items()]
            for x,b in files.items():put(pre+x,b)
            put(pre+'retention.json',dump(dict(attempt=name,actual_child_result=next(c for c in cmds if c['name']==name),
                files_saved_after_attempt=saved,files_before_attempt=prior,meaning='SYNTHETIC TEST ONLY')))
            prior={x['path']:{'bytes':x['bytes'],'sha256':x['sha256']} for x in saved}
    put('source-files-a.stdout','\n'.join(v.PAPER+'/'+x['path'] for x in rows).encode())
    info='Pages: 1\n';put('pdfinfo.stdout',info.encode())
    own=dict(own_runtime=True,runtime_kind='CPU',session_reference='SYNTHETIC_NOT_ACTUAL',observed_at=STAMP,consumption_units=None)
    r=dict(source=v.SOURCE,tex_raw_sha256=v.TEX,input_manifest_sha256=v.INPUTS,status=v.STATUS,tex_argument=v.TEX_ARG,
        source_epoch=v.EPOCH,started_at=STAMP,finished_at=STAMP,math_tests=False,formal_verification=False,new_assessment=None,
        billing_units=None,billing_seconds=None,release_status='OWNED_SESSION_CLOSURE_MUST_BE_OBSERVED_AFTER_RETURN',
        runtime_owner_claim=own,hostname='SYNTHETIC',platform='SYNTHETIC',observed_builder_wall_seconds=1,pages=1,pdfinfo=info,
        commands=cmds,cleanup=[dict(path=v.ROOT+'/clone-'+m,removed=True) for m in ('a','b')],
        builds=[dict(mode=m,source=v.SOURCE,epoch=v.EPOCH,input_files_verified=85,pdf_bytes=len(pdf),pdf_sha256=v.digest(pdf),overfull_lines=[]) for m in ('a','b')])
    put('report.json',dump(r));put('source-binding354.json',dump(dict(source=v.SOURCE,paper=v.PAPER,active_tex_sha256=v.TEX,
        input_manifest_sha256=v.INPUTS,pdf_sha256=v.digest(pdf),tex_argument=v.TEX_ARG,input_files=rows)))
    pp='production-preparation/'
    for n in ('build354D.py','launch354D.py','SOURCE-INPUTS354D.json','PREPARATION-MANIFEST.json','mark_artifact_operation_started.mjs','README.txt'):
        put(pp+n,(v.BASE/'frozen-producer'/n).read_bytes())
    gate=dict(source=v.SOURCE,status='READY_AFTER_ACTUAL_PARENT_REVIEW',reviewed_builder_sha256=v.BUILDER,reviewed_launcher_sha256=v.LAUNCHER,owner_observation=own)
    for key in ('source_integration_review','production_engineering_review','required_ci'):
        content=('SYNTHETIC RECEIPT '+key).encode();n=key+'.txt';put(pp+'gates/'+n,content)
        gate[key]=dict(source=v.SOURCE,status='ACCEPTED',path=n,sha256=v.digest(content))
    gatebytes=dump(gate);put(pp+'gates/authorization.json',gatebytes)
    marker=dict(argv=['node',v.PACKET+'/mark_artifact_operation_started.mjs','--operation-kind','create','--expected-output-count','1','--output-format','pdf'],actual_exit=0,started_at=STAMP,finished_at=STAMP)
    launch=dict(source=v.SOURCE,builder_sha256=v.BUILDER,launcher_sha256=v.LAUNCHER,marker_actual_exit=0,marker=marker,owner_observation=own,gate_sha256=v.digest(gatebytes),created_at=STAMP)
    outer={'launch-receipt354D.json':dump(launch),'launch-result354D.json':dump(dict(source=v.SOURCE,
        builder=dict(argv=['/usr/bin/python3',v.PACKET+'/build354D.py'],actual_exit=0,started_at=STAMP,finished_at=STAMP),
        finished_at=STAMP,owned_runtime_closed=False,billing_units=None,exact_pdf_review=None)),
        'marker354D.stdout':b'','marker354D.stderr':b'','marker354D.exit':b'0\n','builder354D.exit':b'0\n','builder354D.stderr':b''}
    for n in ('launch-receipt354D.json','marker354D.stdout','marker354D.stderr','marker354D.exit'):put(pp+n,outer[n])
    return data,outer

def pack(data,outer):
    stamp_manifest(data,'evidence/manifest.json');inner=zip_bytes(data)
    outer['tep354D-build-01-results.zip']=inner
    outer['builder354D.stdout']=announcement_dump(dict(status=v.STATUS,archive=v.ROOT+'-results.zip',archive_bytes=len(inner),archive_sha256=v.digest(inner)))
    stamp_manifest(outer,'RETURN-MANIFEST.json');return zip_bytes(outer)
def mutate_json(data,name,change):
    obj=v.js(data[name]);change(obj);data[name]=dump(obj)
def report(data,change):mutate_json(data,'evidence/report.json',change)
def binding(data,change):mutate_json(data,'evidence/source-binding354.json',change)
def reject(label,fn):
    try:fn()
    except (ValueError,KeyError,TypeError,FileNotFoundError,zipfile.BadZipFile,UnicodeError):return label
    raise RuntimeError('Guard accepted mutation: '+label)

def preflight():
    results=[];base,outer=fixture()
    good=pack(copy.deepcopy(base),copy.deepcopy(outer));v.validate_bytes(good)
    results.append('positive-full-synthetic-record-including-tex-version-and-four-compiles')
    def case(label,edit):
        data,ot=copy.deepcopy(base),copy.deepcopy(outer);edit(data,ot)
        results.append(reject(label,lambda:v.validate_bytes(pack(data,ot))))
    for suffix,value in [('nonzero',b'7\n'),('empty',b''),('malformed',b'0'),('boolean',b'False\n'),('multiline',b'0\n0\n')]:
        case('native-sentinel-'+suffix,lambda d,o,x=value:d.__setitem__('evidence/tex-a-pass1.exit',x))
    case('native-sentinel-absent',lambda d,o:d.pop('evidence/tex-a-pass1.exit'))
    case('native-stderr-absent',lambda d,o:d.pop('evidence/tex-b-pass2.stderr'))
    case('tex-version-is-not-compile',lambda d,o:report(d,lambda r:r['commands'][2].__setitem__('argv',v.expected_command('tex-a-pass1')[0])))
    case('compile-is-not-version',lambda d,o:report(d,lambda r:next(c for c in r['commands'] if c['name']=='tex-a-pass1').__setitem__('argv',['pdflatex','--version'])))
    case('compile-shell-escape',lambda d,o:report(d,lambda r:next(c for c in r['commands'] if c['name']=='tex-b-pass2')['argv'].__setitem__(1,'-shell-escape')))
    case('native-nonzero-field',lambda d,o:report(d,lambda r:r['commands'][0].__setitem__('actual_exit',1)))
    case('native-bool-field',lambda d,o:report(d,lambda r:r['commands'][0].__setitem__('actual_exit',False)))
    case('native-timeout',lambda d,o:report(d,lambda r:r['commands'][0].__setitem__('timed_out',True)))
    case('native-sequence',lambda d,o:report(d,lambda r:r['commands'].reverse()))
    case('native-cwd',lambda d,o:report(d,lambda r:r['commands'][0].__setitem__('cwd','/content/other')))
    case('native-epoch-environment',lambda d,o:report(d,lambda r:next(c for c in r['commands'] if c['name']=='tex-a-pass1')['environment_controls'].__setitem__('SOURCE_DATE_EPOCH','1')))
    case('source-SHA',lambda d,o:report(d,lambda r:r.__setitem__('source','0'*40)))
    case('input-count',lambda d,o:report(d,lambda r:r['builds'][0].__setitem__('input_files_verified',44)))
    case('duplicate-build',lambda d,o:report(d,lambda r:r['builds'][1].__setitem__('mode','a')))
    case('source-raw-mutation',lambda d,o:d.__setitem__('evidence/source-capture/sources/source349A.txt',b'changed'))
    case('actual-clone-head',lambda d,o:d.__setitem__('evidence/head-b.stdout',b'wrong\n'))
    case('source-files-list',lambda d,o:d.__setitem__('evidence/source-files-a.stdout',b''))
    case('tracked-source-diff',lambda d,o:d.__setitem__('evidence/tracked-diff-a.stdout',b'changed'))
    case('clone-PDF-difference',lambda d,o:d.__setitem__('evidence/clone-b.pdf',b'%PDF-other'))
    case('actual-page-count',lambda d,o:report(d,lambda r:r.__setitem__('pages',2)))
    case('page-absent',lambda d,o:d.pop('evidence/page-1.png'))
    case('PNG-signature',lambda d,o:d.__setitem__('evidence/page-1.png',b'bad'))
    case('contact-absent',lambda d,o:d.pop('evidence/contact-01.jpg'))
    case('content-heading',lambda d,o:d.__setitem__('evidence/manuscript354.txt',b'incomplete'))
    case('PDF-binding',lambda d,o:binding(d,lambda r:r.__setitem__('pdf_sha256','0'*64)))
    case('cleanup-debt',lambda d,o:report(d,lambda r:r['cleanup'][0].__setitem__('removed',False)))
    case('native-retention-child',lambda d,o:mutate_json(d,'evidence/native-tex/tex-a-pass1/retention.json',lambda r:r['actual_child_result'].__setitem__('actual_exit',1)))
    case('native-prior-lineage',lambda d,o:mutate_json(d,'evidence/native-tex/tex-a-pass2/retention.json',lambda r:r.__setitem__('files_before_attempt',{})))
    case('native-raw',lambda d,o:d.__setitem__('evidence/native-tex/tex-a-pass2/production354.aux',b'changed'))
    case('producer-script',lambda d,o:d.__setitem__('evidence/production-preparation/build354D.py',b'changed'))
    case('extra-inner-member',lambda d,o:d.__setitem__('evidence/extra.txt',b'extra'))
    case('marker-exit',lambda d,o:o.__setitem__('marker354D.exit',b'1\n'))
    case('builder-exit-absent',lambda d,o:o.pop('builder354D.exit'))
    case('launch-source',lambda d,o:mutate_json(o,'launch-result354D.json',lambda r:r.__setitem__('source','0'*40)))
    case('invented-runtime-closure',lambda d,o:mutate_json(o,'launch-result354D.json',lambda r:r.__setitem__('owned_runtime_closed',True)))
    case('extra-outer-member',lambda d,o:o.__setitem__('extra.txt',b'x'))
    def gate_edit(d,o,edit):
        n='evidence/production-preparation/gates/authorization.json';g=v.js(d[n]);edit(g);d[n]=dump(g)
        launch=v.js(o['launch-receipt354D.json']);launch['gate_sha256']=v.digest(d[n]);o['launch-receipt354D.json']=dump(launch)
        d['evidence/production-preparation/launch-receipt354D.json']=o['launch-receipt354D.json']
    case('gate-pending-after-rebinding',lambda d,o:gate_edit(d,o,lambda g:g.__setitem__('status','PENDING')))
    case('gate-source-after-rebinding',lambda d,o:gate_edit(d,o,lambda g:g['required_ci'].__setitem__('source','0'*40)))
    case('gate-receipt-raw',lambda d,o:d.__setitem__('evidence/production-preparation/gates/required_ci.txt',b'changed'))
    case('source-input-binding-count',lambda d,o:binding(d,lambda b:b['input_files'].pop()))
    case('invented-mathematical-test',lambda d,o:report(d,lambda r:r.__setitem__('math_tests',True)))
    case('invented-PDF-assessment',lambda d,o:report(d,lambda r:r.__setitem__('new_assessment','passed')))
    case('native-naive-time',lambda d,o:report(d,lambda r:r['commands'][0].__setitem__('started_at','2026-11-14T00:00:00')))
    case('JPEG-signature',lambda d,o:d.__setitem__('evidence/contact-01.jpg',b'bad'))
    return results,good
def atomic_preflight():
    import subprocess,sys
    labels=[]
    def check(ok,label):v.need(ok,label);labels.append(label)
    with tempfile.TemporaryDirectory(prefix='synthetic354A-') as directory:
        root=Path(directory)
        for label,exitcode in (('zero',0),('nonzero',7)):
            actual=subprocess.run([sys.executable,'-c',f'raise SystemExit({exitcode})'],check=False).returncode
            a.publish_exit(root/label,actual)
            check(a.read_exit((root/label).with_suffix('.exit'))==exitcode,'atomic-native-'+label)
        labels.append(reject('reader-rejects-nonzero-success',lambda:a.read_exit(root/'nonzero.exit',True)))
        a.read_exit(root/'zero.exit',True);labels.append('reader-accepts-exact-zero')
        try:a.publish_exit(root/'nonzero',0)
        except (ValueError,FileExistsError):pass
        else:raise RuntimeError('Overwrite accepted')
        check((root/'nonzero.exit').read_bytes()==b'7\n','duplicate-destination-preserved')
        def interrupt():raise RuntimeError('deliberate interrupted publication')
        try:a.publish_exit(root/'interrupt',0,interrupt)
        except RuntimeError:pass
        else:raise RuntimeError('Missing interruption')
        check(not(root/'interrupt.exit').exists() and (root/'interrupt.exit.tmp').read_bytes()==b'0\n','interrupted-temp-not-success')
        labels.append(reject('reader-rejects-unpublished-exit',lambda:a.read_exit(root/'interrupt.exit',True)))
        def race():(root/'race.exit').write_bytes(b'9\n')
        try:a.publish_exit(root/'race',0,race)
        except FileExistsError:pass
        else:raise RuntimeError('Race overwrote destination')
        check((root/'race.exit').read_bytes()==b'9\n','atomic-noreplace-race')
        labels.append(reject('atomic-bool-rejected',lambda:a.publish_exit(root/'bool',False)))
        for label,raw in (('empty',b''),('malformed',b'zero\n'),('multi',b'0\n0\n'),('missing-LF',b'0')):
            p=root/(label+'.exit');p.write_bytes(raw)
            labels.append(reject('reader-'+label,lambda p=p:a.read_exit(p,True)))
        raw=b'SYNTHETIC TRANSPORT BYTES';sha=v.digest(raw);dest=root/'transport.zip'
        a.publish_bytes(dest,raw,len(raw),sha)
        check(dest.read_bytes()==raw,'transport-atomic-write-readback')
        labels.append(reject('transport-length-before-write',lambda:a.publish_bytes(root/'wronglen',raw,len(raw)+1,sha)))
        labels.append(reject('transport-hash-before-write',lambda:a.publish_bytes(root/'wronghash',raw,len(raw),'0'*64)))
        check(not(root/'wronglen').exists() and not(root/'wronghash').exists(),'transport-invalid-never-published')
    return labels
def raw_header_nul_zip(data,member):
    """Write a safe longer alias, then patch ONLY its local/central name byte.
    Equal-length byte substitution preserves offsets, CRCs and every payload.
    A ZIP writer is never asked to write a NUL (which it might sanitize).
    """
    import struct
    alias=member+'XRAW_NUL';alias_raw=alias.encode('utf-8');prefix=member.encode('utf-8')
    v.need(member in data and alias not in data,'Unique raw-header target')
    ordinary=zip_bytes({alias if n==member else n:b for n,b in data.items()})
    with zipfile.ZipFile(io.BytesIO(ordinary)) as z:
        local=z.getinfo(alias).header_offset
    v.need(ordinary[local:local+4]==b'PK\x03\x04','Actual local header')
    local_len=struct.unpack_from('<H',ordinary,local+26)[0]
    local_start=local+30
    v.need(local_len==len(alias_raw) and ordinary[local_start:local_start+local_len]==alias_raw,'Actual raw local name')
    end=ordinary.rfind(b'PK\x05\x06')
    v.need(end>=0 and end+22==len(ordinary),'Fixture ordinary EOCD without comment')
    count=struct.unpack_from('<H',ordinary,end+10)[0]
    offset=struct.unpack_from('<I',ordinary,end+16)[0]
    central_start=None
    for unused in range(count):
        v.need(ordinary[offset:offset+4]==b'PK\x01\x02','Actual central header')
        namelen,extralen,commentlen=struct.unpack_from('<HHH',ordinary,offset+28)
        start=offset+46
        if ordinary[start:start+namelen]==alias_raw:
            v.need(central_start is None,'Unique central target');central_start=start
        offset=start+namelen+extralen+commentlen
    v.need(central_start is not None and offset==end,'Complete central walk')
    local_byte=local_start+len(prefix);central_byte=central_start+len(prefix)
    v.need(ordinary[local_byte]==ordinary[central_byte]==ord('X'),'Placeholder byte in BOTH headers')
    raw=bytearray(ordinary);raw[local_byte]=0;raw[central_byte]=0;raw=bytes(raw)
    expected=prefix+b'\0RAW_NUL'
    v.need(raw[local_start:local_start+len(expected)]==expected
           and raw[central_start:central_start+len(expected)]==expected,'BOTH actual raw names contain NUL')
    v.need([i for i,(a,b) in enumerate(zip(ordinary,raw)) if a!=b]==[local_byte,central_byte],
           'Exactly two name bytes changed; no CRC/payload/offset edits')
    return raw,dict(member=member,local_name_offset=local_start,central_name_offset=central_start,
                    raw_name_hex=expected.hex(),bytes=len(raw),sha256=v.digest(raw),
                    changed_offsets=[local_byte,central_byte])

def raw_header_nul_scenarios(good):
    labels=[];witnesses=[]
    # Outer logical manifest stays for the safe prefix, exactly matching the
    # unchanged payload. The actual transport hash is freshly supplied below.
    outer=v.unpack(good)
    bad,witness=raw_header_nul_zip(outer,'builder354D.stderr')
    cases=[('raw-NUL-outer-local-and-central',bad,dict(layer='outer',**witness))]
    # Inner raw-name attack: retain logical inner manifest/payloads, then rebind
    # actual inner ZIP length/hash announcement AND the full outer raw manifest.
    outer=v.unpack(good);inner=v.unpack(outer['tep354D-build-01-results.zip'])
    bad_inner,witness=raw_header_nul_zip(inner,'evidence/report.json')
    outer['tep354D-build-01-results.zip']=bad_inner
    outer['builder354D.stdout']=announcement_dump(dict(status=v.STATUS,archive=v.ROOT+'-results.zip',
                                         archive_bytes=len(bad_inner),archive_sha256=v.digest(bad_inner)))
    stamp_manifest(outer,'RETURN-MANIFEST.json')
    # Prove the enclosing records are not stale before delivering the attack.
    v.manifest(outer,'RETURN-MANIFEST.json')
    ann=v.js(outer['builder354D.stdout'])
    v.need(ann['archive_bytes']==len(bad_inner) and ann['archive_sha256']==v.digest(bad_inner),'Rebound actual inner announcement')
    bad=zip_bytes(outer)
    cases.append(('raw-NUL-inner-local-and-central-rebound',bad,dict(layer='inner',**witness)))
    with tempfile.TemporaryDirectory(prefix='raw-header354B-') as directory:
        for label,bundle,details in cases:
            path=Path(directory)/(label+'.zip');path.write_bytes(bundle)
            # Matching external length/hash rules out a stale transport binding.
            try:v.validate_file(path,len(bundle),v.digest(bundle))
            except ValueError as exc:
                v.need(str(exc)=='Unsafe path','NUL case rejected at wrong predicate: '+str(exc))
            else:raise RuntimeError('Raw local/central NUL name accepted: '+label)
            labels.append(label);witnesses.append(dict(scenario=label,transport_bytes=len(bundle),
                transport_sha256=v.digest(bundle),rejection='Unsafe path',**details))
    return labels,witnesses

def announcement_scenarios(good):
    # Exact field incident: B used the record-file pretty serializer for stdout.
    # The producer and unchanged validator require one JSON announcement per line.
    outer=v.unpack(good);raw=outer['builder354D.stdout'];ann=v.js(raw)
    v.need(raw==announcement_dump(ann) and len(raw.splitlines())==1,
           'Fixture must match actual producer single-line JSON protocol')
    v.validate_bytes(good)
    labels=['announcement-compact-producer-protocol-positive']
    def rebound(stdout):
        candidate=copy.deepcopy(outer);candidate['builder354D.stdout']=stdout
        stamp_manifest(candidate,'RETURN-MANIFEST.json')
        v.manifest(candidate,'RETURN-MANIFEST.json')
        return zip_bytes(candidate)
    old_pretty=dump(ann)
    v.need(len(old_pretty.splitlines())>1 and old_pretty.splitlines()[0]==b'{',
           'Reproduce original B pretty-print failure field')
    try:v.validate_bytes(rebound(old_pretty))
    except json.JSONDecodeError as exc:
        v.need(exc.pos==1 and exc.lineno==1 and exc.colno==2,
               'Original pretty-JSON regression failed at different parse location')
    else:raise RuntimeError('Original pretty-printed announcement unexpectedly accepted')
    labels.append('announcement-original-B-pretty-JSONDecodeError-preserved')
    for label,stdout in [('announcement-duplicate-rejected',raw+raw),
                         ('announcement-absent-rejected',b'')]:
        try:v.validate_bytes(rebound(stdout))
        except ValueError as exc:
            v.need(str(exc)=='Single actual builder announcement',
                   'Announcement multiplicity case rejected at wrong predicate: '+str(exc))
        else:raise RuntimeError('Invalid announcement multiplicity accepted: '+label)
        labels.append(label)
    return labels
if __name__=='__main__':
    results,good=preflight();results+=announcement_scenarios(good);results+=atomic_preflight()
    nul_labels,nul_witnesses=raw_header_nul_scenarios(good);results+=nul_labels
    for path in ('../escape','/absolute','evidence/../escape','evidence\\bad'):
        data,outer=fixture();data[path]=b'x'
        results.append(reject('zip-path-'+path,lambda data=data,outer=outer:v.validate_bytes(pack(data,outer))))
    data,outer=fixture();data['evidence/Report.json']=b'case-alias'
    results.append(reject('zip-case-alias',lambda:v.validate_bytes(pack(data,outer))))
    ot=v.unpack(good);ot['builder354D.stderr']=b'changed-without-manifest-update'
    results.append(reject('outer-raw-manifest-hash',lambda:v.validate_bytes(zip_bytes(ot))))
    with tempfile.TemporaryDirectory() as folder:
        file=Path(folder)/'fixture.zip';file.write_bytes(good)
        v.validate_file(file,len(good),v.digest(good));results.append('positive-transport-binding')
        results.append(reject('actual-transport-hash',lambda:v.validate_file(file,len(good),'0'*64)))
        results.append(reject('actual-transport-length',lambda:v.validate_file(file,len(good)+1,v.digest(good))))
    out=io.BytesIO()
    with zipfile.ZipFile(out,'w') as z:
        z.writestr('x',b'a');z.writestr('x',b'b')
    results.append(reject('duplicate-ZIP-members',lambda:v.unpack(out.getvalue())))
    out=io.BytesIO()
    with zipfile.ZipFile(out,'w') as z:
        info=zipfile.ZipInfo('link');info.create_system=3;info.external_attr=0o120777<<16;z.writestr(info,b'target')
    results.append(reject('symlink-ZIP-member',lambda:v.unpack(out.getvalue())))
    v.need(len(results)==len(set(results)),'Unique named scenarios')
    print(json.dumps(dict(status='SYNTHETIC_GUARDS_PASSED',fixture_not_actual_pdf=True,
                         optimized=not __debug__,count=len(results),scenarios=results,
                         raw_header_nul_witnesses=nul_witnesses),sort_keys=True))
