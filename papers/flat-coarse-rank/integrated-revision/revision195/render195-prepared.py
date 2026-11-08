"""Frozen offline TeX/render recipe; execute only in this chat's own Colab CPU."""
from datetime import datetime, timezone
import hashlib,json,os,platform,resource,subprocess,sys,tempfile,time,traceback,urllib.request,zipfile
from pathlib import Path

SOURCE='ad4ea990b3fbe14565146ff4d2c904102b5c582e'
PREFIX='papers/flat-coarse-rank/integrated-revision/revision195/'
FILES={'boundary-transfer.tex': 'a71474ff5b3519bbce84cbde1dc9d90efd5746efd06042160f1977d6b7dc76e8', 'detour-separation.tex': 'a7bd1013ac7cfe7b00d3e29913e6ed5e81316a8e304a5aa7343956917f44c268', 'flat_critical_integrated.tex': '9d83e657d31005b7137577b58598164b6558bf8810666fadace9ca89401c3af8', 'laminates-green.tex': '3aa2b0517c400aef0259a353b3d04f0750a4af3d6390d31989bcc1616e236ab1', 'partial-invariance.tex': 'fd2c382bda872858a71b0dc0fd992ce58a509e139e13d5f930de0a59bce50a01', 'partition.tex': '18a864a9e4eb3aeba417d0ea3f9238b67a68886d2fa9901e64c81298a6369be2', 'physical-cycle.tex': 'c06cfc76e02a7c50a83d7f9dbad0fb2b92f23440f330339a16c533fb4494917c', 'sobolev.tex': '65a531612374f0218bff0efac4dfd799cb2dc6a420c6c41ac60ac78f88fb83bb', 'spatial-geometry.tex': 'cfa2bfef60d30f38216d6dd24145e55a2d7353b3d810dee1e8eedfa944fc74d4'}
if platform.system()!='Linux':raise RuntimeError('Own Colab Linux build required')
RECOVERY189B_CONFIRMED=False
if not RECOVERY189B_CONFIRMED:raise RuntimeError('First reconcile and release own189B; this prepared recipe is not yet executable')
ROOT=Path(tempfile.mkdtemp(prefix='tep195-render-',dir='/content'));ev=ROOT/'evidence';ev.mkdir()
start=datetime.now(timezone.utc).isoformat();clock=time.monotonic()
report={'unit':195,'attempt':'A','source_sha':SOURCE,'source_hashes':FILES,'started_utc':start,'steps':[],
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
    audited190={
      'source-audit190.txt':('papers/flat-coarse-rank/research/evidence190/source-audit190.txt','041f7dc6beb3adff674dc65ee5978785b450d5dcf6ea7e3a1e15dc5fd0a9e008'),
      'audit190.json':('papers/flat-coarse-rank/research/evidence190/audit190.json','5877f718d54a95a5557f263e80dac79116744790e55ed091568a7fdad29e1388'),
      'source-proof190.txt':('papers/flat-coarse-rank/research/2026-11-07_detour-separation190.txt','1090cfb751ed667ca625f84003460279ac658df4a0caa839086e6c5eb489f23d')}
    for name,(rel,digest) in audited190.items():
        raw=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/007cf5a7ca98ba99d9e187d075bbcd43557cb16f/'+rel,timeout=45).read()
        if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('Audited190 input mismatch')
        (ev/name).write_bytes(raw)
    boundary_sources={'source-proof192.txt': ('fcedc62d16e08d99bc6e12e22bbd92db302eec3d', 'papers/flat-coarse-rank/research/2026-11-08_neumann-extension192.txt', 'a088b7bb394964ca81f7822c7b579a6a07ec5101f7e5bdc160da06545895b940'), 'source-audit192.txt': ('fcedc62d16e08d99bc6e12e22bbd92db302eec3d', 'papers/flat-coarse-rank/research/evidence192/source-audit192.txt', 'e089b67a331038d246ad453e89a2527c76a9786acce06454eb1da69c37a0acd9'), 'audit192.json': ('fcedc62d16e08d99bc6e12e22bbd92db302eec3d', 'papers/flat-coarse-rank/research/evidence192/audit192.json', '4869b05d7ef0d7354c318043a2fea6589bbae451bd2fecfeb24be79901e22115'), 'AUTHOR-RESPONSE192.txt': ('fcedc62d16e08d99bc6e12e22bbd92db302eec3d', 'papers/flat-coarse-rank/research/evidence192/AUTHOR-RESPONSE192.txt', '0683353cc6fd474431fe67f8ddb91667a09d5534c9b92e7bbb5c51c2cca8d8d4'), 'source-proof193.txt': ('39aa216005cce6e5b4bf36ed4145c6f0a9367a37', 'papers/flat-coarse-rank/research/2026-11-08_capacity-obstruction193.txt', 'a4bb3c201e083a5cf581af6fd4720e0a9deb37b143f62e21a4c5591f3afd2c1c'), 'source-audit193.txt': ('39aa216005cce6e5b4bf36ed4145c6f0a9367a37', 'papers/flat-coarse-rank/research/evidence193/source-audit193.txt', '2d5cd1c2e7f2d9766fa4bd353851caacb4527af6b99e8ce459ad21251ca4db06'), 'audit193.json': ('39aa216005cce6e5b4bf36ed4145c6f0a9367a37', 'papers/flat-coarse-rank/research/evidence193/audit193.json', '41dc34d50ca71621d0911d24efe7d0c01655f10d46a011c6c9aea56ce3c0d00f'), 'AUTHOR-RESPONSE193.txt': ('39aa216005cce6e5b4bf36ed4145c6f0a9367a37', 'papers/flat-coarse-rank/research/evidence193/AUTHOR-RESPONSE193.txt', '90a7f539fc459d1f64c127352473aa654afdecdd557ad0ab31b785d14dad6e49'), 'source-proof194.txt': ('d5fd301c093c71313682bde657f87f0ab10be34e', 'papers/flat-coarse-rank/research/2026-11-08_aggregate-capacity194.txt', '1c94cf9e45a140b0af55b3d24438de37c9840444c8b2ee4ea446334e4c0d42d0'), 'source-audit194.txt': ('d5fd301c093c71313682bde657f87f0ab10be34e', 'papers/flat-coarse-rank/research/evidence194/source-audit194.txt', 'cdb858d858405207e89ca3f4aa42a3e4a449fb1a0b4328b45ec5c01542596b54'), 'audit194.json': ('d5fd301c093c71313682bde657f87f0ab10be34e', 'papers/flat-coarse-rank/research/evidence194/audit194.json', 'e0f77d8cd396e32af826a9113936acf13ca861e2055f71968800bd099c940bd6'), 'AUTHOR-RESPONSE194.txt': ('d5fd301c093c71313682bde657f87f0ab10be34e', 'papers/flat-coarse-rank/research/evidence194/AUTHOR-RESPONSE194.txt', 'aea0d01ba7e0cc6dce17f36e1f31154ef84b00360e3c1419e68701efe997bc4e'), 'source-audit195A.txt': ('ad4ea990b3fbe14565146ff4d2c904102b5c582e', 'papers/flat-coarse-rank/integrated-revision/revision195/evidence195/source-audit195A.txt', '15a11fb55e62375f0a4a18f7b847c4aeaa2cee71a9e2c35a41e1eace8fd69f72'), 'audit195A.json': ('ad4ea990b3fbe14565146ff4d2c904102b5c582e', 'papers/flat-coarse-rank/integrated-revision/revision195/evidence195/audit195A.json', 'ccad2248da61ee2c9ac17173b17d3512341485c4bd71f1f784ab32c9eecea09c'), 'source-audit195B.txt': ('ad4ea990b3fbe14565146ff4d2c904102b5c582e', 'papers/flat-coarse-rank/integrated-revision/revision195/evidence195/source-audit195B.txt', '10a3b381fd736f5aadc51f18d18bbb54480296f8d32ec4c05f7e81cce14b1ea7'), 'audit195B.json': ('ad4ea990b3fbe14565146ff4d2c904102b5c582e', 'papers/flat-coarse-rank/integrated-revision/revision195/evidence195/audit195B.json', 'bdf8b095320790ba639d8568df50c4eeb1db600fd3cf40d8e277691ced36b207'), 'AUTHOR-RESPONSE195.txt': ('ad4ea990b3fbe14565146ff4d2c904102b5c582e', 'papers/flat-coarse-rank/integrated-revision/revision195/evidence195/AUTHOR-RESPONSE195.txt', '32771fb5fced84bfd983dc7a5ce781312944bb8623a7e7bbe73a999555de2dfb')}
    for name,(commit,rel,digest) in boundary_sources.items():
        raw=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+commit+'/'+rel,timeout=45).read()
        if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('Boundary proof/audit input mismatch: '+name)
        (ev/name).write_bytes(raw)
    for name,digest in FILES.items():
        raw=urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/'+PREFIX+name,timeout=45).read()
        if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('Frozen source hash mismatch: '+name)
        (ev/name).write_bytes(raw)
    with zipfile.ZipFile(ev/'source195.zip','w',zipfile.ZIP_DEFLATED) as z:
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
    for required in ('Rectangular means under critical inverse moments','Model assessments and review context','laminate','coexact','Green','retain both positive-start periodic edges','fewer than','648','Distance two suffices','Independence between neighbours is insufficient','D190','Limits of Neumann and harmonic boundary transfer','Disjoint traces do not justify a sum of harmonic costs'):
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
    bundle=Path('/content/tep195-review.zip')
    with zipfile.ZipFile(bundle,'w',zipfile.ZIP_DEFLATED) as z:
        for p in sorted(ev.iterdir()):
            if p.is_file():z.write(p,p.name)
    print('FINAL_REPORT195='+json.dumps(report,sort_keys=True))
    print('BUNDLE195_SHA256='+hashlib.sha256(bundle.read_bytes()).hexdigest())
    print('BUNDLE195_BYTES='+str(bundle.stat().st_size))
    print('BUNDLE195_PATH='+str(bundle))
    import base64
    encoded195=base64.b64encode(bundle.read_bytes()).decode()
    print('EXPORT195_READY_CHUNKS='+str((len(encoded195)+499999)//500000))
    # No automatic large stdout/HTML export. Use the separately prepared bounded helper.
