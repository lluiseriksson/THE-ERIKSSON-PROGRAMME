"""Frozen offline TeX/render recipe; execute only in this chat's own Colab CPU."""
from datetime import datetime, timezone
import hashlib,json,os,platform,resource,subprocess,sys,tempfile,time,traceback,urllib.request,zipfile
from pathlib import Path

SOURCE='aea66c3ee4508b19ecdf6f84cd8d40ba4d8a0d97'
PREFIX='papers/flat-coarse-rank/integrated-revision/revision189/'
FILES={"flat_critical_integrated.tex":"d8f0a6277888af5230b804ffe4b5a0564328852fdeb27d323d517ca229f312da","laminates-green.tex":"3aa2b0517c400aef0259a353b3d04f0750a4af3d6390d31989bcc1616e236ab1","partial-invariance.tex":"fd2c382bda872858a71b0dc0fd992ce58a509e139e13d5f930de0a59bce50a01","partition.tex":"18a864a9e4eb3aeba417d0ea3f9238b67a68886d2fa9901e64c81298a6369be2","physical-cycle.tex":"c06cfc76e02a7c50a83d7f9dbad0fb2b92f23440f330339a16c533fb4494917c","sobolev.tex":"65a531612374f0218bff0efac4dfd799cb2dc6a420c6c41ac60ac78f88fb83bb","spatial-geometry.tex":"cfa2bfef60d30f38216d6dd24145e55a2d7353b3d810dee1e8eedfa944fc74d4"}
if platform.system()!='Linux':raise RuntimeError('Own Colab Linux build required')
ROOT=Path(tempfile.mkdtemp(prefix='tep189-render-',dir='/content'));ev=ROOT/'evidence';ev.mkdir()
start=datetime.now(timezone.utc).isoformat();clock=time.monotonic()
report={'unit':189,'attempt':'B','source_sha':SOURCE,'source_hashes':FILES,'started_utc':start,'steps':[],
        'visual_review':'PENDING','model_assessment':None,'numeric_stars':None,'published':False,
        'execution_plane':'Own Colab Linux CPU','python':platform.python_version(),'independent_review':False}

def run(args,label,timeout=600):
    tick=time.monotonic();child=subprocess.Popen(args,cwd=ev,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    timed_out=False
    try:stdout,stderr=child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out=True;child.kill();stdout,stderr=child.communicate()
    (ev/(label+'.stdout.txt')).write_bytes(stdout);(ev/(label+'.stderr.txt')).write_bytes(stderr)
    tmp=ev/(label+'.exit.tmp');tmp.write_text(str(child.returncode)+'\n');target=ev/(label+'.exit.txt');tmp.replace(target)
    if target.read_text()!=str(child.returncode)+'\n':raise ValueError('Actual exit sentinel mismatch')
    report['steps'].append({'label':label,'exit_code':child.returncode,'seconds':time.monotonic()-tick,'timed_out':timed_out})
    if timed_out or child.returncode:raise RuntimeError(label+' failed; complete evidence preserved')
    return stdout.decode(errors='replace')

try:
    supporting = {
      'supporting-evidence184.zip': (
       'a411c0da84c9962b32ba9e1267169b407f737402/papers/flat-coarse-rank/integrated-revision/revision186/supporting-evidence184.zip',
       'd450902261037f8c76e691cd4debe17477caa64a63ba40abc9e49e951f5c7a5e'),
      'supporting-evidence185.zip': (
       '506004b3e7251aa881b08dde1a1bb14aff33e76f/papers/flat-coarse-rank/research/evidence185/tep185-evidence.zip',
       '7c3659dcc621c90a24762f8277b9310b188df1a2052d9fa51b7d243ec666c1c3')}
    supporting['supporting-evidence188.zip']=('d8d2c66ce76103e302e08cb74f878d46b7a60262/papers/flat-coarse-rank/research/evidence188/tep188-evidence.zip','94f762615a4a7fdc93d04437aa9e2c97bfa4496ea214be6d9dbd078cc5a26fb0')
    for name,(path,digest) in supporting.items():
        raw=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+path,timeout=45).read()
        if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('Supporting raw evidence hash mismatch')
        (ev/name).write_bytes(raw)
    for name,digest in FILES.items():
        raw=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/'+PREFIX+name,timeout=45).read()
        if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('Frozen source hash mismatch: '+name)
        (ev/name).write_bytes(raw)
    with zipfile.ZipFile(ev/'source189.zip','w',zipfile.ZIP_DEFLATED) as z:
        for name in FILES:z.write(ev/name,name)
    run(['apt-get','-qq','update'],'apt-update',600)
    run(['apt-get','install','-y','-qq','texlive-latex-base','texlive-latex-recommended','texlive-fonts-recommended','lmodern','poppler-utils'],'apt-install',900)
    os.environ['SOURCE_DATE_EPOCH']='1794009600';os.environ['FORCE_SOURCE_DATE']='1'
    report['pdflatex_version']=run(['pdflatex','--version'],'pdflatex-version')
    run(['pdftoppm','-v'],'poppler-version')
    report['poppler_version']=(ev/'poppler-version.stderr.txt').read_text()
    for mode in ('first','second','final'):
        run(['pdflatex','-interaction=nonstopmode','-halt-on-error','flat_critical_integrated.tex'],'latex-'+mode,240)
    report['pdfinfo']=run(['pdfinfo','flat_critical_integrated.pdf'],'pdfinfo')
    run(['pdftotext','-layout','flat_critical_integrated.pdf','flat_critical_integrated.txt'],'pdftext')
    text=(ev/'flat_critical_integrated.txt').read_text();joined=' '.join(text.split())
    for required in ('Rectangular means under critical inverse moments','Model assessments and review context','laminate','coexact','Green','retain both positive-start periodic edges','fewer than','648'):
        if required not in joined:raise ValueError('Required new content missing: '+required)
    log=(ev/'flat_critical_integrated.log').read_text(errors='replace')
    warnings=[line for line in log.splitlines() if any(s in line for s in ('Overfull','Undefined','undefined references','LaTeX Warning'))]
    report['layout_warnings']=warnings
    run(['pdftoppm','-r','100','-png','flat_critical_integrated.pdf','page'],'render-pages',300)
    pages=sorted(ev.glob('page-*.png'))
    if not pages:raise ValueError('No exact-PDF rendered pages')
    from PIL import Image,ImageDraw
    for block,offset in enumerate(range(0,len(pages),6),1):
        sheet=Image.new('RGB',(840,1160),'#dddddd')
        for i,path in enumerate(pages[offset:offset+6]):
            with Image.open(path) as src:
                pic=src.convert('RGB');pic.thumbnail((400,540))
                tile=Image.new('RGB',(420,580),'white');tile.paste(pic,((420-pic.width)//2,12));ImageDraw.Draw(tile).text((10,558),path.name,fill='black')
                sheet.paste(tile,((i%2)*420,(i//2)*580))
        # Three rows are required for six pages.
        if len(pages[offset:offset+6])>4:
            sheet=Image.new('RGB',(840,1740),'#dddddd')
            for i,path in enumerate(pages[offset:offset+6]):
                with Image.open(path) as src:
                    pic=src.convert('RGB');pic.thumbnail((400,540))
                    tile=Image.new('RGB',(420,580),'white');tile.paste(pic,((420-pic.width)//2,12));ImageDraw.Draw(tile).text((10,558),path.name,fill='black')
                    sheet.paste(tile,((i%2)*420,(i//2)*580))
        sheet.save(ev/('contact-'+str(block).zfill(2)+'.png'))
        sheet.save(ev/('contact-'+str(block).zfill(2)+'.jpg'),quality=85,optimize=True)
    pdf=ev/'flat_critical_integrated.pdf'
    report.update(status='PDF_RENDERED_PENDING_VISUAL_REVIEW',page_count=len(pages),pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),pdf_bytes=pdf.stat().st_size)
    if warnings:raise ValueError('Final layout/citation warning; preserve and correct before review')
except Exception:
    report['status']='FAILED_PRESERVED';(ev/'failure.txt').write_text(traceback.format_exc())
finally:
    report.update(finished_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-clock,
                  child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,compute_units_billed=None)
    (ev/'report.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    manifest=[{'path':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(ev.iterdir()) if p.is_file()]
    (ev/'manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
    bundle=Path('/content/tep189-review.zip')
    with zipfile.ZipFile(bundle,'w',zipfile.ZIP_DEFLATED) as z:
        for p in sorted(ev.iterdir()):
            if p.is_file():z.write(p,p.name)
    print('FINAL_REPORT189='+json.dumps(report,sort_keys=True))
    print('BUNDLE189_SHA256='+hashlib.sha256(bundle.read_bytes()).hexdigest())
    print('BUNDLE189_BYTES='+str(bundle.stat().st_size))
    print('BUNDLE189_PATH='+str(bundle))
    import base64
    encoded189=base64.b64encode(bundle.read_bytes()).decode()
    core=Path('/content/tep189-core.zip')
    with zipfile.ZipFile(core,'w',zipfile.ZIP_DEFLATED) as z:
        for p in sorted(ev.iterdir()):
            if p.is_file() and p.suffix!='.png':z.write(p,p.name)
    rawcore=core.read_bytes()
    print('CORE189_SHA256='+hashlib.sha256(rawcore).hexdigest())
    print('CORE189_BYTES='+str(len(rawcore)))
    print('EXPORT189='+base64.b64encode(rawcore).decode())
