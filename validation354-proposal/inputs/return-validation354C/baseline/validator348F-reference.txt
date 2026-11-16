"""UNEXECUTED UI inner-return validator348E. Linux only; not an assessment or proof.
Exact348A inner archive checks retained; UI observation replaces CLI outer preconditions.
"""
from pathlib import Path, PurePosixPath
import json, hashlib, re, zipfile, os

if os.name != 'posix' or not Path('/content').is_dir():
    raise RuntimeError('Own Colab Linux only; no Windows import or execution')

EXPECTED_INPUT_COUNT = 44
SOURCE = 'a27c28cbfd506b7ad06aeebb8b141df89d6a0cba'
TEX = '0a851ffb2e6b6a7c4a491266f6fdd2e22dcd4efc3c234cc5a57b86719f63319d'
SUPPORT = 'c273a2ada5308dacddcf6b28d615aa2e9721fa89f0e0c8fd6f48ac97738b127b'
TEX_ARG = (r'\pdfinfoomitdate=1\pdftrailerid{}'
           r'\ifdefined\pdfsuppressptexinfo\pdfsuppressptexinfo=15\fi'
           r'\input{manuscript347.tex}')
STATUS = 'TWO_FRESH_MATCHING_PDFS_RENDERED_PENDING_ALL_PAGE_VISUAL_AND_FIRST_EXACT_PDF_ASSESSMENT'
COMMANDS = ['apt-update','apt-install','tex-version','poppler-version','git-version']
for mode in ('a','b'):
    COMMANDS += ['clone-'+mode,'head-'+mode,'sparse-init-'+mode,'sparse-set-'+mode,'checkout-'+mode]
    if mode == 'a': COMMANDS += ['source-files-a']
    COMMANDS += ['epoch-'+mode,'tex-'+mode+'-pass1','tex-'+mode+'-pass2','tracked-diff-'+mode]
COMMANDS += ['pdfinfo','extract','render']

def require(ok, message):
    if not ok: raise ValueError(message)

def digest(raw): return hashlib.sha256(raw).hexdigest()

def check_zero(raw): require(raw == b'0\n', 'Exact single-line zero sentinel required')

def fresh(paths):
    require(len(paths)==len(set(map(str, paths))), 'Repeated destination')
    for path in paths:
        require(not path.exists() and not path.is_symlink(), 'Existing destination: '+str(path))
        for parent in path.parents:
            require(not parent.is_symlink(), 'Symlink parent')

def safe_names(names):
    seen=set()
    for name in names:
        require(isinstance(name,str) and name and '\\' not in name, 'Invalid archive path')
        parts=name.split('/')
        require(not PurePosixPath(name).is_absolute(), 'Absolute path')
        for part in parts:
            require(part not in ('','.','..') and part==part.rstrip(' .'), 'Aliased path')
            require(not re.search(r'[\x00-\x1f<>:"|?*]', part), 'Windows unsafe name')
            require(part.split('.')[0].upper() not in {'CON','PRN','AUX','NUL',*[f'COM{i}' for i in range(1,10)],*[f'LPT{i}' for i in range(1,10)]}, 'Reserved name')
        folded=name.casefold()
        require(folded not in seen, 'Duplicate/case alias')
        seen.add(folded)
    for name in seen:
        parts=name.split('/')
        require(not any('/'.join(parts[:i]) in seen for i in range(1,len(parts))), 'File/directory collision')

def check_ui_observation(observation, archive, attempt):
    require(set(observation)=={'schema','source','builder_sha256','source_manifest_sha256','started_at','finished_at','child','files','archive','marker'}, 'Exact UI observation schema; no CLI lifecycle fields')
    require(observation['schema']=='tep348-ui-inner-transport-v1' and observation['source']==SOURCE, 'UI source/schema')
    require(observation['builder_sha256']=='bf93b063004f3dcb811af97e1585114508d0cd4d47cbb3dae48bf0ae7bad30b2', 'Repinned builder identity')
    require(observation['source_manifest_sha256']=='d1b6be5a51570e564ae7da9dd01af6fc7a6fd4ace8a9a8a251f7e470c63a5221', '44-source binding identity')
    from datetime import datetime
    started=datetime.fromisoformat(observation['started_at']); finished=datetime.fromisoformat(observation['finished_at'])
    require(started.tzinfo is not None and finished.tzinfo is not None and finished>=started, 'Actual UTC interval')
    child=observation['child']
    require(set(child)=={'argv','actual_exit','termination_observed','timed_out','interrupted','launch_or_wait_error'}, 'Exact child observation fields')
    require(type(child['actual_exit']) is int and child['actual_exit']==0 and child['termination_observed'] is True and child['timed_out'] is False and child['interrupted'] is False and child['launch_or_wait_error'] is None, 'Actual successful builder child required')
    argv=child['argv']
    require(isinstance(argv,list) and len(argv)==2 and isinstance(argv[0],str) and argv[0].startswith('/') and argv[1]=='/content/ui-production348D/build348.py', 'Actual builder argv')
    marker=observation['marker']
    require(isinstance(marker,dict) and set(marker)=={'argv','script_sha256','actual_exit','completed_without_interruption'}, 'Actual marker observation')
    require(type(marker['actual_exit']) is int and marker['actual_exit']==0 and marker['completed_without_interruption'] is True and marker['script_sha256']=='968d66a7b491c7728f2ab009dcb54ac0025d6f474de6f3734f66b8809f6c18a8', 'Successful exact official marker')
    require(isinstance(marker['argv'],list) and len(marker['argv'])==8 and isinstance(marker['argv'][0],str) and marker['argv'][0].startswith('/') and marker['argv'][1:]==['/content/ui-production348D/mark_artifact_operation_started.mjs','--operation-kind','create','--expected-output-count','1','--output-format','pdf'], 'Exact official marker command')
    required={'builder.stdout','builder.stderr','builder.exit','authority-gates.zip','synthetic-preflight.zip','marker.stdout','marker.stderr','marker.exit'}
    require(set(observation['files'])==required, 'Exact observed transport files')
    for name in required:
        row=observation['files'][name]; path=attempt/name
        require(set(row)=={'bytes','sha256'} and type(row['bytes']) is int and row['bytes']>=0 and re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None, 'Observed file metadata')
        require(path.is_file() and not path.is_symlink() and path.stat().st_size==row['bytes'] and digest(path.read_bytes())==row['sha256'], 'Observed raw file differs: '+name)
    check_zero((attempt/'builder.exit').read_bytes())
    check_zero((attempt/'marker.exit').read_bytes())
    row=observation['archive']
    require(isinstance(row,dict) and set(row)=={'remote_path','bytes','sha256'} and row['remote_path']=='/content/tep348D-build-a-results.zip', 'Actual archive identity')
    require(type(row['bytes']) is int and row['bytes']>0 and re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None, 'Actual archive metadata')
    require(archive.is_file() and not archive.is_symlink() and archive.stat().st_size==row['bytes'] and digest(archive.read_bytes())==row['sha256'], 'UI archive bytes')


def check_native_tex_commands(commands):
    require([c['name'] for c in commands] == COMMANDS, 'Exact native command sequence')
    compile_names = {'tex-a-pass1', 'tex-a-pass2', 'tex-b-pass1', 'tex-b-pass2'}
    for c in commands:
        if c['name'] == 'tex-version':
            require(c['argv'] == ['pdflatex', '--version'], 'Exact native TeX version argv')
        elif c['name'] in compile_names:
            require(c['argv'] == ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error',
                                 '-file-line-error', '-jobname=production348', TEX_ARG], 'Exact native TeX compile argv')

def check_report(report):
    require(report['source']==SOURCE and report['tex_raw_sha256']==TEX and report['status']==STATUS, 'Report subject/status')
    require(report['support_raw_sha256']==SUPPORT and report['tex_argument']==TEX_ARG, 'Included source and deterministic argument')
    builds=report['builds']
    require(len(builds)==2 and [x['mode'] for x in builds]==['a','b'], 'Two unique builds required')
    for b in builds:
        require(b['source']==SOURCE and type(b['input_files_verified']) is int and b['input_files_verified']==EXPECTED_INPUT_COUNT, 'Build inputs/source')
        require(type(b['pdf_bytes']) is int and b['pdf_bytes']>0 and re.fullmatch('[0-9a-f]{64}',b['pdf_sha256']) is not None, 'Build PDF')
        require(isinstance(b['epoch'],str) and re.fullmatch('[0-9]+',b['epoch']) is not None, 'Build epoch')
    require(all(builds[0][k]==builds[1][k] for k in ('epoch','pdf_bytes','pdf_sha256')), 'Different builds')
    require([x['name'] for x in report['commands']]==COMMANDS, 'Exact native command sequence')
    for c in report['commands']:
        require(type(c['actual_exit']) is int and c['actual_exit']==0 and c['timed_out'] is False, 'Native exit/timeout')
        require(isinstance(c['argv'],list) and c['argv'] and all(isinstance(x,str) for x in c['argv']), 'Native argv')
    cleanup=report['cleanup']
    require(len(cleanup)==2 and [c['path'] for c in cleanup]==['/content/tep348D-build-a/clone-a','/content/tep348D-build-a/clone-b'], 'Exact cleanup paths')
    require(all(c['removed'] is True and 'error' not in c for c in cleanup), 'Cleanup failure')
    require(type(report['pages']) is int and 1<=report['pages']<=60, 'Page count')

def check_manifest(rows, names):
    require(isinstance(rows,list) and rows, 'Empty manifest')
    paths=[r['path'] for r in rows]
    safe_names(paths)
    require(set(paths)==set(names)-{'evidence/manifest.json'}, 'Manifest coverage')
    for row in rows:
        require(type(row['bytes']) is int and row['bytes']>=0 and re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None, 'Manifest types')

def validate(archive, attempt, source_manifest, destinations):
    fresh(destinations)
    require(digest(source_manifest.read_bytes())=='d1b6be5a51570e564ae7da9dd01af6fc7a6fd4ace8a9a8a251f7e470c63a5221', 'Pinned source inventory')
    observation=json.loads((attempt/'ui-observation.json').read_bytes())
    check_ui_observation(observation,archive,attempt)
    announcements=[]
    for line in (attempt/'builder.stdout').read_text(encoding='utf-8-sig').splitlines():
        if line.startswith('{'):
            value=json.loads(line)
            if 'archive_sha256' in value: announcements.append(value)
    require(len(announcements)==1, 'Actual builder archive announcement')
    ann=announcements[0]
    require(ann['archive']=='/content/tep348D-build-a-results.zip' and ann['status']==STATUS, 'Remote archive identity')
    require(type(ann['archive_bytes']) is int and archive.stat().st_size==ann['archive_bytes'] and digest(archive.read_bytes())==ann['archive_sha256'], 'Actual builder archive bytes')
    declared=json.loads(source_manifest.read_bytes())['files']
    prefix='papers/stationary-doob347/'
    require(len(declared)==EXPECTED_INPUT_COUNT and all(row['path'].startswith(prefix) for row in declared),'Repository-relative declared input universe')
    expected=[{'path':row['path'][len(prefix):],'bytes':row['bytes'],'raw_sha256':row['sha256']} for row in declared]
    safe_names([r['path'] for r in expected]);require(len(expected)==EXPECTED_INPUT_COUNT, 'Frozen input inventory')
    with zipfile.ZipFile(archive) as z:
        infos=z.infolist();names=[i.filename for i in infos];safe_names(names)
        require(0<len(names)<5000 and sum(i.file_size for i in infos)<512_000_000, 'Archive bounds')
        require(all(not i.is_dir() and (i.external_attr>>16)&0o170000 in (0,0o100000) and not (i.flag_bits&1) for i in infos), 'Archive unencrypted regular files')
        require('evidence/manifest.json' in names, 'No manifest')
        rows=json.loads(z.read('evidence/manifest.json'));check_manifest(rows,names)
        for row in rows:
            raw=z.read(row['path'])
            require(len(raw)==row['bytes'] and digest(raw)==row['sha256'], 'Raw member mismatch '+row['path'])
        r=json.loads(z.read('evidence/report.json'));check_report(r)
        captured={n.removeprefix('evidence/source-capture/') for n in names if n.startswith('evidence/source-capture/')}
        require(captured=={x['path'] for x in expected}, 'Exact44 captured source inventory')
        for row in expected:
            raw=z.read('evidence/source-capture/'+row['path'])
            require(len(raw)==row['bytes'] and digest(raw)==row['raw_sha256'], 'Captured source differs')
        require(digest(z.read('evidence/source-capture/manuscript347.tex'))==TEX, 'Captured TeX')
        require(digest(z.read('evidence/source-capture/support346-section.tex'))==SUPPORT, 'Captured included TeX')
        check_native_tex_commands(r['commands'])
        for c in r['commands']:
            require(z.read('evidence/'+c['name']+'.exit')==b'0\n', 'Actual native exit')
            for ext in ('.stdout','.stderr'): require('evidence/'+c['name']+ext in names, 'Missing native log')
        for mode in ('a','b'):
            require(z.read('evidence/head-'+mode+'.stdout').decode().strip()==SOURCE, 'Actual source head')
            require(z.read('evidence/epoch-'+mode+'.stdout').decode().strip()==r['builds'][0]['epoch'], 'Actual source epoch')
            require(not z.read('evidence/tracked-diff-'+mode+'.stdout').strip(), 'Tracked source changed')
        pdf=z.read('evidence/manuscript347.pdf')
        require(pdf.startswith(b'%PDF-') and len(pdf)==r['builds'][0]['pdf_bytes'] and digest(pdf)==r['builds'][0]['pdf_sha256'], 'Canonical PDF')
        require(all(z.read('evidence/clone-'+m+'.pdf')==pdf for m in ('a','b')), 'Actual PDFs differ')
        info=z.read('evidence/pdfinfo.stdout').decode();match=re.search(r'(?m)^Pages:\s+(\d+)\s*$',info)
        require(match is not None and int(match.group(1))==r['pages'] and info==r['pdfinfo'], 'Actual pdfinfo')
        pages={n for n in names if re.fullmatch(r'evidence/page-[0-9]+\.png',n)}
        require(len(pages)==r['pages'] and {int(n.split('-')[-1].split('.')[0]) for n in pages}==set(range(1,r['pages']+1)), 'Page inventory')
        contacts={n for n in names if re.fullmatch(r'evidence/contact-[0-9]+\.jpg',n)}
        require(contacts=={f'evidence/contact-{i:02d}.jpg' for i in range(1,(r['pages']+3)//4+1)}, 'Contact inventory')
        require(all(z.read(n).startswith(b'\x89PNG\r\n\x1a\n') for n in pages), 'Actual PNG headers')
        extracted=z.read('evidence/manuscript347.txt').decode();normal=' '.join(extracted.split())
        for marker in ('Stationary marginals and bottleneck restrictions for Boolean Doob kernels',
                       'The model and the theorem map','Quantitative rigidity of the smoothed potential',
                       'An admissible failure of uniform convergence','The imported weighting theorem and its exact role',
                       'Actual cut capacities above the rare-mass threshold','Small supports without a marginal matching assumption',
                       'Classical scaling and the unresolved comparison','Model assessments and review context'):
            require(marker in normal, 'Missing exact347 content marker '+marker)
        require(len(extracted)>15000 and '??' not in extracted and '[SLOT]' not in extracted, 'Incomplete PDF extraction')
        binding=json.loads(z.read('evidence/source-binding348.json'))
        require(binding['source']==SOURCE and binding['paper']=='papers/stationary-doob347' and
                binding['active_tex_sha256']==TEX and binding['support_tex_sha256']==SUPPORT and
                binding['pdf_sha256']==digest(pdf) and binding['tex_argument']==TEX_ARG, 'Raw source/PDF binding')
        require({(x['path'],x['bytes'],x['sha256']) for x in binding['input_files']}==
                {(x['path'],x['bytes'],x['raw_sha256']) for x in expected} and len(binding['input_files'])==44, 'Binding exact source universe')
        require('evidence/failure.txt' not in names and 'evidence/cleanup-pending.txt' not in names, 'Recorded failure/debt')
        universe={'evidence/'+n for n in ('report.json','manifest.json','source-binding348.json','manuscript347.pdf','manuscript347.txt','clone-a.pdf','clone-b.pdf','clone-a-latex.log','clone-b-latex.log')}
        universe |= {'evidence/'+c+ext for c in COMMANDS for ext in ('.exit','.stdout','.stderr')}
        universe |= {'evidence/source-capture/'+n for n in captured} | pages | contacts
        for mode in ('a','b'):
            for passno in (1,2):
                name=f'tex-{mode}-pass{passno}';prefix='evidence/native-tex/'+name+'/'
                retention=json.loads(z.read(prefix+'retention.json'))
                require(retention['attempt']==name and retention['actual_child_result']==next(c for c in r['commands'] if c['name']==name), 'Native retention child binding')
                saved=retention['files_saved_after_attempt'];safe_names([x['path'] for x in saved])
                require({x['path'] for x in saved}=={'manuscript347.tex','support346-section.tex'}|
                        {'production348'+ext for ext in ('.pdf','.log','.aux','.out')}, 'Native retained inventory')
                for item in saved:
                    raw=z.read(prefix+item['path'])
                    require(len(raw)==item['bytes'] and digest(raw)==item['sha256'], 'Native retained bytes')
                require(digest(z.read(prefix+'manuscript347.tex'))==TEX, 'Native TeX')
                require(digest(z.read(prefix+'support346-section.tex'))==SUPPORT, 'Native included TeX')
                if passno==2: require(z.read(prefix+'production348.pdf')==pdf, 'Final native PDF')
                universe |= {prefix+x['path'] for x in saved} | {prefix+'retention.json'}
        require(set(names)==universe, 'Unexpected/missing archive artifact')
    return {'source':SOURCE,'PDF_sha256':digest(pdf),'PDF_bytes':len(pdf),'pages':r['pages'],'archive_sha256':digest(archive.read_bytes()),'raw_members_verified':len(rows),'source_input_members_verified':EXPECTED_INPUT_COUNT,'scope':'Exact raw declared inventories, bindings and exits checked; parent must read native logs/argv/retention, verify runtime inactivity, inspect all pages and assess exact PDF. Not independent proof of execution or mathematics.'}
