"""Prepared offline; create and render only in this chat's own Colab Linux CPU."""
import base64
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import sys
import time
import traceback
import urllib.request
import zipfile

SOURCE = '776d2741e7350ca30705691a50d5411924c6b39d'
PATH = 'papers/flat-coarse-rank/integrated-revision/revision171/flat_critical_integrated.tex'
EXPECTED = '7d3b9b0a9a098927d82bc5c68354ac0e8308878855db7440a159f8325e7e4e76'
ROOT = Path('/content/tep-own171-integrated')
if not sys.platform.startswith('linux'):
    raise RuntimeError('Own Colab Linux required')
ROOT.mkdir(exist_ok=False)
ev = ROOT/'evidence'
ev.mkdir()
started = datetime.now(timezone.utc)
clock = time.monotonic()
report = {'unit': 171, 'attempt': 'A', 'source_sha': SOURCE, 'tex_git_LF_sha256': EXPECTED,
          'started_utc': started.isoformat(), 'python': platform.python_version(),
          'platform': platform.platform(), 'gpu_environment': os.environ.get('COLAB_GPU', ''),
          'visual_review': 'PENDING', 'independent_review': False,
          'external_model_score': None, 'published': False, 'steps': []}


def run(args, label, timeout=600):
    tick = time.monotonic()
    child = subprocess.run(args, cwd=ev, capture_output=True, timeout=timeout)
    (ev/(label+'.stdout.txt')).write_bytes(child.stdout)
    (ev/(label+'.stderr.txt')).write_bytes(child.stderr)
    tmp = ev/(label+'.exit.tmp')
    tmp.write_text(str(child.returncode)+'\n')
    if tmp.read_text().strip() != str(child.returncode):
        raise ValueError('Exit sentinel mismatch')
    tmp.replace(ev/(label+'.exit.txt'))
    report['steps'].append({'label': label, 'exit_code': child.returncode,
                            'seconds': time.monotonic()-tick})
    if child.returncode:
        raise RuntimeError(label+' failed; complete logs retained')
    return child.stdout.decode(errors='replace')


try:
    raw = urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/'+PATH, timeout=45).read()
    if hashlib.sha256(raw).hexdigest() != EXPECTED:
        raise ValueError('Pinned TeX source mismatch')
    (ev/'flat_critical_integrated.tex').write_bytes(raw)
    dependency_hashes = {'partition.tex': '18a864a9e4eb3aeba417d0ea3f9238b67a68886d2fa9901e64c81298a6369be2', 'physical-cycle.tex': 'c06cfc76e02a7c50a83d7f9dbad0fb2b92f23440f330339a16c533fb4494917c', 'sobolev.tex': '879f895b69eb04fd41c26fd4e4bd779dcdfe7d9547c22181c6d4313f343bdb43'}
    for name, expected in dependency_hashes.items():
        data = urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/papers/flat-coarse-rank/integrated-revision/revision171/'+name, timeout=45).read()
        if hashlib.sha256(data).hexdigest() != expected:
            raise ValueError('Dependency hash mismatch: '+name)
        (ev/name).write_bytes(data)
    run(['apt-get', '-qq', 'update'], 'apt-update', 600)
    run(['apt-get', 'install', '-y', '-qq', 'texlive-latex-base', 'texlive-latex-recommended',
         'texlive-fonts-recommended', 'lmodern', 'poppler-utils'], 'apt-install', 900)
    os.environ['SOURCE_DATE_EPOCH'] = str(int(datetime(2026, 11, 6, tzinfo=timezone.utc).timestamp()))
    os.environ['FORCE_SOURCE_DATE'] = '1'
    report['pdflatex_version'] = run(['pdflatex', '--version'], 'pdflatex-version')
    run(['pdftoppm', '-v'], 'poppler-version')
    report['poppler_version'] = (ev/'poppler-version.stderr.txt').read_text()
    run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'flat_critical_integrated.tex'], 'latex-first', 180)
    run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'flat_critical_integrated.tex'], 'latex-second', 180)
    run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'flat_critical_integrated.tex'], 'latex-final', 180)
    info = run(['pdfinfo', 'flat_critical_integrated.pdf'], 'pdfinfo')
    run(['pdftotext', '-layout', 'flat_critical_integrated.pdf', 'flat_critical_integrated.txt'], 'pdftext')
    text = (ev/'flat_critical_integrated.txt').read_text()
    joined = ' '.join(text.split())
    if 'Model assessments and review context' not in joined or '80/33' not in joined or 'coexact' not in joined or '16/(5' not in joined or '3529' not in joined or 'full optimum' not in joined:
        raise ValueError('Required appendix content absent from final PDF extraction')
    run(['pdftoppm', '-r', '100', '-jpeg', '-jpegopt', 'quality=90', 'flat_critical_integrated.pdf', 'page'], 'render-pages', 240)
    pages = sorted(ev.glob('page-*.jpg'))
    if not pages:
        raise ValueError('No rendered pages')
    from PIL import Image, ImageDraw
    width = 250
    thumbs = []
    for page in pages:
        with Image.open(page) as source:
            img = source.convert('RGB')
            img.thumbnail((width, 380))
            tile = Image.new('RGB', (width+12, 405), 'white')
            tile.paste(img, ((width+12-img.width)//2, 20))
            ImageDraw.Draw(tile).text((8, 388), page.name, fill='black')
            thumbs.append(tile)
    sheet = Image.new('RGB', (3*(width+12), ((len(thumbs)+2)//3)*405), '#dddddd')
    for i, tile in enumerate(thumbs):
        sheet.paste(tile, ((i % 3)*(width+12), (i//3)*405))
    sheet.save(ev/'contact-sheet.png')
    log = (ev/'flat_critical_integrated.log').read_text(errors='replace')
    warnings = [line for line in log.splitlines() if any(term in line for term in
                ('Overfull', 'Undefined', 'undefined references', 'LaTeX Warning'))]
    report.update(status='PDF_RENDERED_PENDING_VISUAL_REVIEW',
                  pdf_sha256=hashlib.sha256((ev/'flat_critical_integrated.pdf').read_bytes()).hexdigest(),
                  pdf_bytes=(ev/'flat_critical_integrated.pdf').stat().st_size,
                  page_count=len(pages), pdfinfo=info, layout_warnings=warnings)
except Exception:
    report['status'] = 'FAILED_PRESERVED'
    (ev/'failure.txt').write_text(traceback.format_exc())
finally:
    report.update(finished_utc=datetime.now(timezone.utc).isoformat(),
                  elapsed_seconds=time.monotonic()-clock,
                  child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                  compute_units_billed=None)
    (ev/'report.json').write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
    manifest = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(ev.iterdir()) if p.is_file()}
    (ev/'manifest.json').write_text(json.dumps(manifest, sort_keys=True, indent=2)+'\n')
    bundle = ROOT/'review171.zip'
    with zipfile.ZipFile(bundle, 'w', zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(ev.iterdir()):
            archive.write(path, path.name)
    print('FINAL_REPORT171='+json.dumps(report, sort_keys=True))
    print('BUNDLE171_SHA256='+hashlib.sha256(bundle.read_bytes()).hexdigest())
    print('REVIEW171_BYTES='+str(bundle.stat().st_size))
    if report['status'] == 'FAILED_PRESERVED':
        raise RuntimeError('Rendering failed; full evidence retained')
