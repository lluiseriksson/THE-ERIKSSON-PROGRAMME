"""Frozen Linux-only production: two fresh sparse clones, matching PDFs, all pages.
No scientific test, grading, deposit, permission or publication is performed.
"""
import os,sys,json,hashlib,subprocess,traceback,zipfile,re,shutil
from pathlib import Path
from datetime import datetime,timezone
SOURCE='375047fac74dee4e464031f7e5b4d2368d5276fa'
BRANCH='codex/tep-tail-manuscript305-20261113'
TEX_SHA='6a0606e994cedcf0107dc700edf2c9b9b762fa8ef4d31da8a958cf3501c0fa65'
PAPER='papers/marginal-transfer'
ROOT=Path('/content/tep305-build-a');OUT=ROOT/'evidence'
ARCHIVE=Path('/content/tep305-build-a-results.zip')
def require(ok,msg):
    if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def utc():return datetime.now(timezone.utc).isoformat()
def put(p,obj):p.write_bytes((json.dumps(obj,indent=2)+'\n').encode())
require(os.name=='posix' and Path('/content').is_dir(),'Own Colab Linux only')
require(not ROOT.exists() and not ARCHIVE.exists(),'Fresh preserved attempt required')
OUT.mkdir(parents=True);commands=[];clones=[];cleanup=[];status='FAILED_PRESERVED'
report={'source':SOURCE,'tex_raw_sha256':TEX_SHA,'started_at':utc(),'python_version':sys.version,'math_tests':False,'formal_verification':False,'new_assessment':None,'billing_units':None,'billing_seconds':None}
def atomic_exit(path,actual):
    require(type(actual) is int and not path.exists(),'New actual child exit required')
    temp=path.with_name(path.name+'.tmp')
    with temp.open('x',encoding='ascii',newline='\n') as f:f.write(str(actual)+'\n');f.flush();os.fsync(f.fileno())
    raw=temp.read_bytes();require(re.fullmatch(rb'-?[0-9]+\n',raw) is not None and int(raw)==actual,'Closed real integer exit')
    os.replace(temp,path);require(path.read_bytes()==raw,'Exit readback differs')
def run(name,args,cwd=None,timeout=600,env=None):
    started=utc();timed_out=False
    with (OUT/(name+'.stdout')).open('xb') as so,(OUT/(name+'.stderr')).open('xb') as se:
        child=subprocess.Popen(args,cwd=cwd or ROOT,stdout=so,stderr=se,env=env)
        try:actual=child.wait(timeout=timeout)
        except subprocess.TimeoutExpired:timed_out=True;child.kill();actual=child.wait()
        so.flush();os.fsync(so.fileno());se.flush();os.fsync(se.fileno())
    atomic_exit(OUT/(name+'.exit'),actual)
    commands.append({'name':name,'argv':args,'actual_exit':actual,'timed_out':timed_out,'started_at':started,'finished_at':utc()})
    require(actual==0 and not timed_out,'Child failed '+name)
    return (OUT/(name+'.stdout')).read_text(errors='replace')
try:
    run('apt-update',['apt-get','-qq','update'],timeout=600)
    run('apt-install',['apt-get','install','-y','-qq','texlive-latex-base','texlive-latex-recommended','lmodern','poppler-utils'],timeout=1200)
    run('tex-version',['pdflatex','--version']);run('poppler-version',['pdftoppm','-v']);run('git-version',['git','--version'])
    builds=[]
    for mode in ('a','b'):
        clone=ROOT/('clone-'+mode);clones.append(clone)
        run('clone-'+mode,['git','clone','--filter=blob:none','--depth','1','--no-checkout','--branch',BRANCH,'https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git',str(clone)],timeout=900)
        actual=run('head-'+mode,['git','rev-parse','HEAD'],clone).strip();require(actual==SOURCE,'Exact source changed')
        run('sparse-init-'+mode,['git','sparse-checkout','init','--cone'],clone)
        run('sparse-set-'+mode,['git','sparse-checkout','set',PAPER],clone)
        run('checkout-'+mode,['git','checkout','--detach',SOURCE],clone,timeout=900)
        paper=clone/PAPER;tex=paper/'manuscript305A.tex'
        require(sha(tex.read_bytes())==TEX_SHA,'Exact audited manuscript differs')
        inputs=json.loads((paper/'SOURCE-INPUTS305.json').read_bytes())['files']
        for row in inputs:
            f=paper/row['path'];require(f.resolve().is_relative_to(paper.resolve()),'Unsafe input path')
            raw=f.read_bytes();require(len(raw)==row['bytes'] and sha(raw)==row['raw_sha256'],'Frozen input differs '+row['path'])
        require(len(inputs)>0,'Nonempty frozen input inventory required')
        if mode=='a':
            # Capture the actual frozen Git-tracked paper inputs, not generated build files.
            names=run('source-files-a',['git','ls-files','--',PAPER],clone).splitlines()
            for name in names:
                rel=Path(name).relative_to(PAPER);dest=OUT/'source-capture'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((clone/name).read_bytes())
        epoch=run('epoch-'+mode,['git','show','-s','--format=%ct',SOURCE],clone).strip()
        require(re.fullmatch(r'[0-9]+',epoch) is not None,'Actual source epoch missing')
        env=dict(os.environ,SOURCE_DATE_EPOCH=epoch,FORCE_SOURCE_DATE='1',TZ='UTC',LC_ALL='C.UTF-8')
        arg='\\def\\SourceCommit{'+SOURCE+'}\\input{manuscript305A.tex}'
        for passno in (1,2):
            name='tex-'+mode+'-pass'+str(passno)
            prior={f.name:{'bytes':f.stat().st_size,'sha256':sha(f.read_bytes())} for f in paper.glob('manuscript305A*') if f.is_file() and not f.is_symlink()}
            try:
                run(name,['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error','-jobname=manuscript305A',arg],paper,timeout=600,env=env)
            finally:
                # Harvest the actual native files before failure propagates, cleanup,
                # or a later pass overwrites them. Never regenerate a failed output.
                dest=OUT/'native-tex'/name;dest.mkdir(parents=True,exist_ok=False)
                saved=[]
                for f in sorted(paper.glob('manuscript305A*')):
                    require(not f.is_symlink(),'Unexpected native build symlink')
                    if f.is_file():
                        raw=f.read_bytes();(dest/f.name).write_bytes(raw)
                        saved.append({'path':f.name,'bytes':len(raw),'sha256':sha(raw)})
                observed=[c for c in commands if c['name']==name]
                put(dest/'retention.json',{'attempt':name,'actual_child_result':observed[-1] if observed else None,'files_before_attempt':prior,'files_saved_after_attempt':saved,'meaning':'Saved files may include preexisting output from an earlier pass; file presence is never proof of a successful or new PDF. Use actual child exit/log.'})
        pdf=paper/'manuscript305A.pdf';raw=pdf.read_bytes();require(raw.startswith(b'%PDF'),'No actual PDF')
        (OUT/('clone-'+mode+'.pdf')).write_bytes(raw)
        log=(paper/'manuscript305A.log').read_bytes();(OUT/('clone-'+mode+'-latex.log')).write_bytes(log)
        diff=run('tracked-diff-'+mode,['git','diff','--exit-code',SOURCE,'--',PAPER],clone)
        require(not diff.strip(),'Tracked source changed during build')
        builds.append({'mode':mode,'source':actual,'epoch':epoch,'pdf_bytes':len(raw),'pdf_sha256':sha(raw),'input_files_verified':len(inputs),'overfull_lines':[l for l in log.decode(errors='replace').splitlines() if 'Overfull' in l]})
    require(builds[0]['pdf_sha256']==builds[1]['pdf_sha256'] and builds[0]['pdf_bytes']==builds[1]['pdf_bytes'],'Two fresh same-source PDFs differ; preserve both')
    report['builds']=builds;pdf=OUT/'manuscript305A.pdf';pdf.write_bytes((OUT/'clone-a.pdf').read_bytes())
    info=run('pdfinfo',['pdfinfo',str(pdf)]);report['pdfinfo']=info
    match=re.search(r'(?m)^Pages:\s+(\d+)\s*$',info);require(match is not None,'Actual page count missing');count=int(match.group(1));require(1<=count<=60,'Unexpected page count')
    run('extract',['pdftotext','-layout',str(pdf),str(OUT/'manuscript305A.txt')])
    text=(OUT/'manuscript305A.txt').read_text();normal=' '.join(text.split())
    for token in (SOURCE,'Model assessments and review context','Codes with two distance conditions','A finite positive concentration estimate','Stationary marginals survive the Perron transform','An exact parity control with different dynamics','Auxiliary critical estimates and an explicit rate','The exact critical moment budget','The escaped critical-moment boundary','The fixed-cutoff endpoint'):
        require(token in normal,'Actual PDF missing expected content '+token)
    require('[SLOT]' not in text and 'SOURCE-NOT-BUILT' not in text,'Unresolved manuscript placeholder')
    require(len(text)>12000,'Unexpectedly short extraction')
    run('render',['pdftoppm','-r','110','-png',str(pdf),str(OUT/'page')],timeout=900)
    pages=sorted(OUT.glob('page-*.png'));require(len(pages)==count,'All-page rendering incomplete')
    from PIL import Image,ImageDraw,__version__ as pillow_version
    report['pillow_version']=pillow_version
    for offset in range(0,count,4):
        sheet=Image.new('RGB',(1040,1480),'#dddddd')
        for j,path in enumerate(pages[offset:offset+4]):
            with Image.open(path) as im:
                im=im.convert('RGB');im.thumbnail((500,700));sheet.paste(im,((j%2)*520+(520-im.width)//2,(j//2)*740+5))
            ImageDraw.Draw(sheet).text(((j%2)*520+10,(j//2)*740+714),path.name,fill='black')
        sheet.save(OUT/('contact-'+str(offset//4+1).zfill(2)+'.jpg'),quality=93)
    report['pages']=count;status='TWO_FRESH_MATCHING_PDFS_RENDERED_PENDING_ALL_PAGE_VISUAL_AND_FIRST_EXACT_PDF_ASSESSMENT'
except Exception:
    (OUT/'failure.txt').write_text(traceback.format_exc(),encoding='utf-8')
finally:
    for clone in clones:
        try:
            require(clone.parent==ROOT and clone.name in ('clone-a','clone-b'),'Exact disposable clone cleanup boundary')
            if clone.exists():shutil.rmtree(clone)
            cleanup.append({'path':str(clone),'removed':not clone.exists()})
        except Exception as exc:cleanup.append({'path':str(clone),'removed':False,'error':str(exc)})
    debts=[c for c in cleanup if not c['removed']]
    if debts:
        status='FAILED_PRESERVED'
        lines=['CLEANUP-PENDING: '+c['path'] for c in debts]
        (OUT/'cleanup-pending.txt').write_text('\n'.join(lines)+'\n',encoding='utf-8')
        for line in lines:print(line)
    report.update(status=status,commands=commands,cleanup=cleanup,finished_at=utc());put(OUT/'report.json',report)
    files=[p for p in sorted(OUT.rglob('*')) if p.is_file()]
    put(OUT/'manifest.json',[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in files])
    with zipfile.ZipFile(ARCHIVE,'x',zipfile.ZIP_DEFLATED) as z:
        for p in sorted(OUT.rglob('*')):
            if p.is_file():z.write(p,p.relative_to(ROOT).as_posix())
print(json.dumps({'status':status,'archive':str(ARCHIVE),'archive_bytes':ARCHIVE.stat().st_size,'archive_sha256':sha(ARCHIVE.read_bytes())}))
if status=='FAILED_PRESERVED':raise RuntimeError('Production failed; preserve all evidence, no blind retry')
