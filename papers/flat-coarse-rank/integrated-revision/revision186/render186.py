"""Frozen offline TeX/render recipe; execute only in this chat's own Colab CPU."""
from datetime import datetime, timezone
import hashlib,json,os,platform,resource,subprocess,sys,tempfile,time,traceback,urllib.request,zipfile
from pathlib import Path

SOURCE='fda4743d41960bf2c0cb018e113cccb85d62ca9a'
PREFIX='papers/flat-coarse-rank/integrated-revision/revision186/'
FILES={'rectangular_observations.tex':'5d7b005ea32af993899746b3584b795df1998ef51bfa943d8f4ba3b4b3d0917a'}
if platform.system()!='Linux':raise RuntimeError('Own Colab Linux build required')
ROOT=Path(tempfile.mkdtemp(prefix='tep186-render-',dir='/content'));ev=ROOT/'evidence';ev.mkdir()
start=datetime.now(timezone.utc).isoformat();clock=time.monotonic()
report={'unit':186,'attempt':'B','source_sha':SOURCE,'source_hashes':FILES,'started_utc':start,'steps':[],
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
    for name,digest in FILES.items():
        raw=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/'+PREFIX+name,timeout=45).read()
        if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('Frozen source hash mismatch: '+name)
        (ev/name).write_bytes(raw)
    with zipfile.ZipFile(ev/'source186.zip','w',zipfile.ZIP_DEFLATED) as z:
        for name in FILES:z.write(ev/name,name)
    run(['apt-get','-qq','update'],'apt-update',600)
    run(['apt-get','install','-y','-qq','texlive-latex-base','texlive-latex-recommended','texlive-fonts-recommended','lmodern','poppler-utils'],'apt-install',900)
    os.environ['SOURCE_DATE_EPOCH']='1794009600';os.environ['FORCE_SOURCE_DATE']='1'
    report['pdflatex_version']=run(['pdflatex','--version'],'pdflatex-version')
    run(['pdftoppm','-v'],'poppler-version')
    report['poppler_version']=(ev/'poppler-version.stderr.txt').read_text()
    for mode in ('first','second','final'):
        run(['pdflatex','-interaction=nonstopmode','-halt-on-error','rectangular_observations.tex'],'latex-'+mode,240)
    report['pdfinfo']=run(['pdfinfo','rectangular_observations.pdf'],'pdfinfo')
    run(['pdftotext','-layout','rectangular_observations.pdf','rectangular_observations.txt'],'pdftext')
    text=(ev/'rectangular_observations.txt').read_text();joined=' '.join(text.split())
    for required in ('Rectangular mean observations','Model assessments and review context','laminate','coexact','Green'):
        if required not in joined:raise ValueError('Required new content missing: '+required)
    log=(ev/'rectangular_observations.log').read_text(errors='replace')
    warnings=[line for line in log.splitlines() if any(s in line for s in ('Overfull','Undefined','undefined references','LaTeX Warning'))]
    report['layout_warnings']=warnings
    run(['pdftoppm','-r','100','-png','rectangular_observations.pdf','page'],'render-pages',300)
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
    pdf=ev/'rectangular_observations.pdf'
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
    bundle=Path('/content/tep186-review.zip')
    with zipfile.ZipFile(bundle,'w',zipfile.ZIP_DEFLATED) as z:
        for p in sorted(ev.iterdir()):
            if p.is_file():z.write(p,p.name)
    print('FINAL_REPORT186='+json.dumps(report,sort_keys=True))
    print('BUNDLE186_SHA256='+hashlib.sha256(bundle.read_bytes()).hexdigest())
    print('BUNDLE186_BYTES='+str(bundle.stat().st_size))
    print('BUNDLE186_PATH='+str(bundle))
    import base64
    print('EXPORT186='+base64.b64encode(bundle.read_bytes()).decode())