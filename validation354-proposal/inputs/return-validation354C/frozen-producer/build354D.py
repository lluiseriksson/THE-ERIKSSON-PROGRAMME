"""UNEXECUTED Linux-only PDF production354; no mathematical test or assessment.
Adapted from the actual348D producer (itself343 recovery-derived). Source bytes stay frozen.
"""
import os, sys, json, hashlib, subprocess, traceback, zipfile, re, shutil, signal, time, platform
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone

SOURCE = '8e452190b8f7d3f7382ba2e6c05d0f14fa9c3dc5'
BRANCH = 'codex/tep-weighting354-source-20261114'
PAPER = 'papers/stationary-weighting354'
TEX_SHA = 'b8cbd2a1b1d817a6889f2219134213b0a9bdeaf20e77d006cebfedcbb59e9233'
INPUTS_SHA = 'cf80a4263ff21f87508ba33a2ebe17b8a4dcad3ca1018651e9ec057dc1970370'
EPOCH = '1794629658'
PACKET = Path(__file__).resolve().parent
ROOT = Path('/content/tep354D-build-01')
OUT = ROOT / 'evidence'
ARCHIVE = Path('/content/tep354D-build-01-results.zip')
STATUS = 'TWO_FRESH_MATCHING_PDFS_RENDERED_PENDING_ALL_PAGE_VISUAL_AND_FIRST_EXACT_PDF_ASSESSMENT'
# Reproducibility metadata only: no visible text, mathematics or source edit.
TEX_ARG = (r'\pdfinfoomitdate=1\pdftrailerid{}'
           r'\ifdefined\pdfsuppressptexinfo\pdfsuppressptexinfo=15\fi'
           r'\input{manuscript354.tex}')
MARKERS = ('Stationary-to-weighting moment transfer and spectral rigidity',
           'Setting and theorem map', 'Failure of exact critical-cap transfer',
           'Inverse moments and subcritical transfer',
           'Full-chain estimates for code-supported potentials',
           'Disjoint blocks and a strictly larger potential class',
           'Positive-rate families at every sufficiently large length',
           'Positioning, failed routes and remaining question',
           'Model assessments and review context')

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def utc():
    return datetime.now(timezone.utc).isoformat()

def put(path, value):
    with path.open('xb') as stream:
        stream.write((json.dumps(value, indent=2) + '\n').encode('utf-8'))

def safe_relative(name):
    require(isinstance(name, str) and name and '\\' not in name, 'Input name')
    require(not PurePosixPath(name).is_absolute() and
            all(p not in ('', '.', '..') for p in name.split('/')), 'Input traversal')
    return name

require(os.name == 'posix' and Path('/content').resolve() == Path('/content')
        and Path('/content').is_dir(), 'Own Colab Linux only')
require(not ROOT.exists() and not ROOT.is_symlink() and
        not ARCHIVE.exists() and not ARCHIVE.is_symlink(), 'Fresh preserved attempt required')
# A real, separately reviewed launch receipt is necessary, not evidence of
# manuscript acceptance by itself. The parent must inspect the attached receipts.
launch = PACKET / 'launch-receipt354D.json'
require(launch.is_file() and not launch.is_symlink(), 'Run reviewed launch354D.py first')
launch_record = json.loads(launch.read_bytes())
require(launch_record['source'] == SOURCE and launch_record['builder_sha256'] == sha(Path(__file__).read_bytes())
        and launch_record['marker_actual_exit'] == 0, 'Launch binding/marker failed')
frozen_raw = (PACKET / 'SOURCE-INPUTS354D.json').read_bytes()
require(sha(frozen_raw) == INPUTS_SHA, 'Frozen input manifest changed')
frozen = json.loads(frozen_raw)
require(frozen['source'] == SOURCE and frozen['paper'] == PAPER and frozen['branch'] == BRANCH
        and str(frozen['commit_epoch']) == EPOCH and len(frozen['entries']) == 85, 'Frozen identity differs')
wall_started = time.monotonic()
OUT.mkdir(parents=True)
commands, clones, cleanup, builds = [], [], [], []
status = 'FAILED_PRESERVED'
report = {'source': SOURCE, 'tex_raw_sha256': TEX_SHA, 'input_manifest_sha256': INPUTS_SHA,
          'started_at': utc(), 'python_version': sys.version, 'math_tests': False,
          'formal_verification': False, 'new_assessment': None,
          'billing_units': None, 'billing_seconds': None, 'tex_argument': TEX_ARG}

def atomic_exit(path, actual):
    require(type(actual) is int and not path.exists(), 'New actual exit required')
    temporary = path.with_name(path.name + '.tmp')
    with temporary.open('x', encoding='ascii', newline='\n') as stream:
        stream.write(str(actual) + '\n'); stream.flush(); os.fsync(stream.fileno())
    raw = temporary.read_bytes()
    require(re.fullmatch(rb'-?[0-9]+\n', raw) is not None and int(raw) == actual,
            'Closed real integer exit')
    os.replace(temporary, path)
    require(path.read_bytes() == raw, 'Exit readback differs')

def run(name, argv, cwd=None, timeout=600, env=None):
    started, timed_out = utc(), False
    with (OUT / (name + '.stdout')).open('xb') as stdout, (OUT / (name + '.stderr')).open('xb') as stderr:
        child = subprocess.Popen(argv, cwd=cwd or ROOT, stdout=stdout, stderr=stderr, env=env, start_new_session=True)
        try:
            actual = child.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True; os.killpg(child.pid, signal.SIGKILL); actual = child.wait()
        stdout.flush(); os.fsync(stdout.fileno()); stderr.flush(); os.fsync(stderr.fileno())
    atomic_exit(OUT / (name + '.exit'), actual)
    commands.append({'name': name, 'argv': argv, 'actual_exit': actual, 'timed_out': timed_out,
                     'cwd': str(cwd or ROOT), 'environment_controls': {k: env[k] for k in ('SOURCE_DATE_EPOCH', 'FORCE_SOURCE_DATE', 'TZ', 'LC_ALL')} if env else {},
                     'started_at': started, 'finished_at': utc()})
    require(actual == 0 and not timed_out, 'Child failed ' + name)
    return (OUT / (name + '.stdout')).read_text(errors='replace')

try:
    provenance = OUT / 'production-preparation'; provenance.mkdir()
    for name in ('build354D.py', 'launch354D.py', 'SOURCE-INPUTS354D.json',
                 'launch-receipt354D.json', 'marker354D.stdout', 'marker354D.stderr', 'marker354D.exit',
                 'PREPARATION-MANIFEST.json', 'mark_artifact_operation_started.mjs', 'README.txt'):
        raw = (PACKET / name).read_bytes(); (provenance / name).write_bytes(raw)
    shutil.copytree(PACKET / 'gates', provenance / 'gates', symlinks=False)
    report.update(hostname=platform.node(), platform=platform.platform(),
                  runtime_owner_claim=launch_record['owner_observation'],
                  release_status='OWNED_SESSION_CLOSURE_MUST_BE_OBSERVED_AFTER_RETURN',
                  source_epoch=EPOCH, runtime_ui_consumption=None,
                  filesystem_free_bytes_start=shutil.disk_usage(ROOT).free)
    run('apt-update', ['apt-get', '-qq', 'update'])
    run('apt-install', ['apt-get', 'install', '-y', '-qq', 'texlive-latex-base',
                       'texlive-latex-recommended', 'lmodern', 'poppler-utils', 'python3-pil'], timeout=1200)
    run('tex-version', ['pdflatex', '--version'])
    run('poppler-version', ['pdftoppm', '-v'])
    run('git-version', ['git', '--version'])
    for mode in ('a', 'b'):
        clone = ROOT / ('clone-' + mode); clones.append(clone)
        run('clone-' + mode, ['git', 'clone', '--filter=blob:none', '--depth', '1', '--no-checkout',
                             '--branch', BRANCH, 'https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git',
                             str(clone)], timeout=900)
        actual = run('head-' + mode, ['git', 'rev-parse', 'HEAD'], clone).strip()
        require(actual == SOURCE, 'Frozen branch HEAD changed; no fallback source')
        run('sparse-init-' + mode, ['git', 'sparse-checkout', 'init', '--cone'], clone)
        run('sparse-set-' + mode, ['git', 'sparse-checkout', 'set', PAPER], clone)
        run('checkout-' + mode, ['git', 'checkout', '--detach', SOURCE], clone, timeout=900)
        paper = clone / PAPER
        inventory = {}
        for row in frozen['entries']:
            name = safe_relative(row['path'])
            require(name not in inventory, 'Duplicate frozen path')
            path = paper / name
            require(path.resolve().is_relative_to(paper.resolve()) and path.is_file()
                    and not path.is_symlink(), 'Unsafe source input')
            raw = path.read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(raw)).encode('ascii') + b'\0' + raw).hexdigest()
            require(len(raw) == row['bytes'] and sha(raw) == row['sha256']
                    and blob == row['git_blob_sha1'], 'Raw frozen blob differs: ' + name)
            inventory[name] = dict(row)
        require(len(inventory) == 85 and sha((paper / 'manuscript354.tex').read_bytes()) == TEX_SHA,
                'Complete frozen source identity')
        if mode == 'a':
            names = run('source-files-a', ['git', 'ls-files', '--', PAPER], clone).splitlines()
            require(set(names) == {PAPER + '/' + name for name in inventory}, 'Exact tracked source universe')
            for name in inventory:
                dest = OUT / 'source-capture' / name
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes((paper / name).read_bytes())
        epoch = run('epoch-' + mode, ['git', 'show', '-s', '--format=%ct', SOURCE], clone).strip()
        require(epoch == EPOCH, 'Actual source epoch differs from frozen commit')
        env = dict(os.environ, SOURCE_DATE_EPOCH=epoch, FORCE_SOURCE_DATE='1', TZ='UTC', LC_ALL='C.UTF-8')
        for passno in (1, 2):
            name = 'tex-' + mode + '-pass' + str(passno)
            def native_paths():
                return [paper / 'manuscript354.tex'] + sorted(paper.glob('production354*'))
            prior = {p.name: {'bytes': p.stat().st_size, 'sha256': sha(p.read_bytes())}
                     for p in native_paths() if p.is_file() and not p.is_symlink()}
            try:
                run(name, ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error',
                           '-file-line-error', '-jobname=production354', TEX_ARG], paper, env=env)
            finally:
                dest = OUT / 'native-tex' / name; dest.mkdir(parents=True, exist_ok=False)
                saved = []
                for path in native_paths():
                    require(not path.is_symlink(), 'Unexpected native symlink')
                    if path.is_file():
                        raw = path.read_bytes(); (dest / path.name).write_bytes(raw)
                        saved.append({'path': path.name, 'bytes': len(raw), 'sha256': sha(raw)})
                observed = [c for c in commands if c['name'] == name]
                put(dest / 'retention.json', {'attempt': name, 'actual_child_result': observed[-1] if observed else None,
                                            'files_before_attempt': prior, 'files_saved_after_attempt': saved,
                                            'meaning': 'Presence may be preexisting output; actual exit/log determines success.'})
        raw = (paper / 'production354.pdf').read_bytes()
        require(raw.startswith(b'%PDF-'), 'No actual PDF')
        (OUT / ('clone-' + mode + '.pdf')).write_bytes(raw)
        log = (paper / 'production354.log').read_bytes(); (OUT / ('clone-' + mode + '-latex.log')).write_bytes(log)
        require(b'There were undefined references' not in log and b'Citation `' not in log,
                'Unresolved final-pass references/citations')
        diff = run('tracked-diff-' + mode, ['git', 'diff', '--exit-code', SOURCE, '--', PAPER], clone)
        require(not diff.strip(), 'Tracked source changed during build')
        builds.append({'mode': mode, 'source': actual, 'epoch': epoch, 'pdf_bytes': len(raw),
                       'pdf_sha256': sha(raw), 'input_files_verified': len(inventory),
                       'overfull_lines': [line for line in log.decode(errors='replace').splitlines() if 'Overfull' in line]})
    require(builds[0]['pdf_sha256'] == builds[1]['pdf_sha256'] and
            builds[0]['pdf_bytes'] == builds[1]['pdf_bytes'], 'Fresh-clone PDFs differ; preserve both')
    report['builds'] = builds
    pdf = OUT / 'manuscript354.pdf'; pdf.write_bytes((OUT / 'clone-a.pdf').read_bytes())
    put(OUT / 'source-binding354.json', {'source': SOURCE, 'paper': PAPER, 'active_tex_sha256': TEX_SHA,
                                       'input_manifest_sha256': INPUTS_SHA, 'pdf_sha256': sha(pdf.read_bytes()),
                                       'tex_argument': TEX_ARG, 'input_files': list(inventory.values())})
    info = run('pdfinfo', ['pdfinfo', str(pdf)]); report['pdfinfo'] = info
    match = re.search(r'(?m)^Pages:\s+(\d+)\s*$', info)
    require(match is not None, 'Actual page count missing')
    count = int(match.group(1)); require(1 <= count <= 60, 'Unexpected page count')
    run('extract', ['pdftotext', '-layout', str(pdf), str(OUT / 'manuscript354.txt')])
    text = (OUT / 'manuscript354.txt').read_text(); normal = ' '.join(text.split())
    for marker in MARKERS:
        require(marker in normal, 'Actual PDF missing content marker ' + marker)
    require(bool(text.strip()) and '??' not in text and '[SLOT]' not in text, 'Incomplete extraction/reference')
    run('render', ['pdftoppm', '-r', '110', '-png', str(pdf), str(OUT / 'page')], timeout=900)
    pages = sorted(OUT.glob('page-*.png'), key=lambda p: int(p.stem.split('-')[-1]))
    require(len(pages) == count and [int(p.stem.split('-')[-1]) for p in pages] == list(range(1, count+1)), 'All pages required')
    from PIL import Image, ImageDraw, __version__ as pillow_version
    report['pillow_version'] = pillow_version
    for offset in range(0, count, 4):
        sheet = Image.new('RGB', (1040, 1480), '#dddddd')
        for j, path in enumerate(pages[offset:offset+4]):
            with Image.open(path) as im:
                im = im.convert('RGB'); im.thumbnail((500, 700))
                sheet.paste(im, ((j % 2)*520+(520-im.width)//2, (j // 2)*740+5))
            ImageDraw.Draw(sheet).text(((j % 2)*520+10, (j // 2)*740+714), path.name, fill='black')
        sheet.save(OUT / ('contact-' + str(offset//4+1).zfill(2) + '.jpg'), quality=93)
    report['pages'] = count; status = STATUS
except Exception:
    (OUT / 'failure.txt').write_text(traceback.format_exc(), encoding='utf-8')
finally:
    for clone in clones:
        try:
            require(clone.parent == ROOT and clone.name in ('clone-a', 'clone-b')
                    and not clone.is_symlink() and clone.resolve().parent == ROOT.resolve(), 'Disposable clone boundary')
            if clone.exists(): shutil.rmtree(clone)
            cleanup.append({'path': str(clone), 'removed': not clone.exists()})
        except Exception as exc:
            cleanup.append({'path': str(clone), 'removed': False, 'error': str(exc)})
    debts = [c for c in cleanup if not c['removed']]
    if debts:
        status = 'FAILED_PRESERVED'
        lines = ['CLEANUP-PENDING: ' + c['path'] for c in debts]
        (OUT / 'cleanup-pending.txt').write_text('\n'.join(lines)+'\n', encoding='utf-8')
        for line in lines: print(line)
    report.update(status=status, commands=commands, cleanup=cleanup, builds=builds, finished_at=utc(),
                  observed_builder_wall_seconds=time.monotonic()-wall_started,
                  filesystem_free_bytes_end=shutil.disk_usage(ROOT).free)
    put(OUT / 'report.json', report)
    files = [p for p in sorted(OUT.rglob('*')) if p.is_file()]
    put(OUT / 'manifest.json', [{'path': p.relative_to(ROOT).as_posix(), 'bytes': p.stat().st_size,
                                'sha256': sha(p.read_bytes())} for p in files])
    with zipfile.ZipFile(ARCHIVE, 'x', zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(OUT.rglob('*')):
            if path.is_file(): archive.write(path, path.relative_to(ROOT).as_posix())
print(json.dumps({'status': status, 'archive': str(ARCHIVE), 'archive_bytes': ARCHIVE.stat().st_size,
                  'archive_sha256': sha(ARCHIVE.read_bytes())}))
if status == 'FAILED_PRESERVED':
    raise RuntimeError('Production failed; retain all evidence, no blind retry')
