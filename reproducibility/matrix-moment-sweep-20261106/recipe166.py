"""Prepared disconnected; execute only in this chat's own Colab Linux CPU."""
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
import zipfile

SOURCE = 'e422859386cd07db2c107c8ab1a21067e99f44bb'
FOLDER = 'reproducibility/matrix-moment-sweep-20261106'
HASHES = {'exact165.py': '2c7c609fbfd317068ff6f76d4aecf2a2325b649248c4ed07d75a69f1d7e6ae5f', 'exact166.py': '0cbb620fe89acb464eb82d1673beb4e4781986f52e532095b6e2c182615ac20d', 'coexact-rectangle166.txt': 'bf30bebdf32dc27ccc58bb16425e9509c8ae101c4d6d6cfb9da0e709fdc5b681'}
ROOT = Path('/content/tep-own166-coexact-rectangle')
if not sys.platform.startswith('linux'):
    raise RuntimeError('Own Colab Linux required')
ROOT.mkdir(exist_ok=False)
ev = ROOT/'evidence'
ev.mkdir()
started = datetime.now(timezone.utc)
clock = time.monotonic()
report = {'unit': 166, 'source_sha': SOURCE, 'expected_git_LF_hashes': HASHES,
          'started_utc': started.isoformat(), 'python': platform.python_version(),
          'platform': platform.platform(), 'gpu_environment': os.environ.get('COLAB_GPU', ''),
          'steps': [], 'independent_review': False, 'Lean_verified': False,
          'all_size_theorem_verified': False, 'fresh_runtime_pair_completed': False}


def command(args, folder, label, timeout=180):
    tick = time.monotonic()
    run = subprocess.run(args, cwd=folder, capture_output=True, timeout=timeout)
    for suffix, value in (('stdout.txt', run.stdout), ('stderr.txt', run.stderr)):
        (ev/(label+'.'+suffix)).write_bytes(value)
    # Exit sentinel published only after process completion.
    tmp = ev/(label+'.exit.tmp')
    final = ev/(label+'.exit.txt')
    tmp.write_text(str(run.returncode)+'\n')
    if tmp.read_text().strip() != str(run.returncode):
        raise ValueError('Exit sentinel readback mismatch')
    tmp.replace(final)
    report['steps'].append({'label': label, 'exit_code': run.returncode,
                            'seconds': time.monotonic()-tick})
    if run.returncode:
        raise ValueError(label+' failed; full logs preserved')
    return run.stdout


try:
    outputs = []
    clones = []
    for name in ('fresh_a', 'fresh_b'):
        folder = ROOT/name
        command(['git', 'clone', '--depth=1', '--filter=blob:none', '--sparse', '--no-checkout',
                 '--single-branch', '--branch', 'codex/tep-matrix-defect-replay-20261106',
                 'https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git', str(folder)], ROOT, name+'-clone')
        command(['git', 'sparse-checkout', 'set', FOLDER], folder, name+'-sparse')
        command(['git', 'fetch', '--depth=1', 'origin', SOURCE], folder, name+'-fetch')
        command(['git', 'checkout', '--detach', SOURCE], folder, name+'-checkout')
        actual = command(['git', 'rev-parse', 'HEAD'], folder, name+'-head').decode().strip()
        if actual != SOURCE:
            raise ValueError('Pinned git HEAD mismatch')
        status = command(['git', 'status', '--porcelain'], folder, name+'-status').decode()
        if status.strip():
            raise ValueError('Fresh clone not clean before execution')
        for script, expected in HASHES.items():
            raw = (folder/FOLDER/script).read_bytes()
            if hashlib.sha256(raw).hexdigest() != expected:
                raise ValueError('Git LF source mismatch: '+script)
            (ev/(name+'-'+script)).write_bytes(raw)
        clones.append({'name': name, 'head': actual, 'clean_before_execution': True,
                       'method': 'actual fresh filtered sparse git clone, pinned fetch and detached checkout'})
        for mode, flags in (('normal', []), ('optimized', ['-O'])):
            payload = command([sys.executable, *flags, str(folder/FOLDER/'exact166.py')],
                              folder/FOLDER, name+'-'+mode, timeout=240)
            row = json.loads(payload)
            if row.get('status') != 'EXACT_COEXACT_RECTANGLE_PASS' or row.get('mutation_count') != 4 or row.get('physical_dimension') != 72:
                raise ValueError('Explicit diagnostic counters mismatch')
            outputs.append(payload)
    if len(outputs) != 4 or any(value != outputs[0] for value in outputs):
        raise ValueError('Fresh-clone normal/-O outputs differ')
    report.update(status='EXACT_COEXACT_RECTANGLE_PASS', clones=clones,
                  process_replays=4, normal_optimized_byte_identical=True,
                  payload_sha256=hashlib.sha256(outputs[0]).hexdigest(),
                  payload=json.loads(outputs[0]))
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
    bundle = ROOT/'evidence166.zip'
    with zipfile.ZipFile(bundle, 'w', zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(ev.iterdir()):
            archive.write(path, path.name)
    print('FINAL_REPORT166='+json.dumps(report, sort_keys=True))
    print('BUNDLE166_SHA256='+hashlib.sha256(bundle.read_bytes()).hexdigest())
    print('EVIDENCE166_BASE64='+base64.b64encode(bundle.read_bytes()).decode())
    if report['status'] != 'EXACT_COEXACT_RECTANGLE_PASS':
        raise RuntimeError('Diagnostics failed; complete evidence preserved')
