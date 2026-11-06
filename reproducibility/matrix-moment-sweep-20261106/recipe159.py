"""Prepared offline. Execute only in this chat's own Colab Linux CPU runtime."""
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

SOURCE = 'a8bf1445f35ba033076bd89e6881e4014b0fe312'
SCRIPT = 'reproducibility/matrix-moment-sweep-20261106/exact159.py'
EXPECTED = '8b509a83fbd799581b41d60d493fe36e86c04124be47453f38da4d1e0ea6e07a'
ROOT = Path('/content/tep-own159-matrix-defect')
if not sys.platform.startswith('linux'):
    raise RuntimeError('Own Colab Linux runtime required')
ROOT.mkdir(exist_ok=False)
ev = ROOT/'evidence'
ev.mkdir()
started = datetime.now(timezone.utc)
clock = time.monotonic()
report = {'unit': 159, 'thread': 'consolidar-e-investigar-the-eriksson-programme-en-airr', 'source_sha': SOURCE, 'script_sha256': EXPECTED, 'started_utc': started.isoformat(), 'python': platform.python_version(), 'platform': platform.platform(), 'gpu_environment': os.environ.get('COLAB_GPU', ''), 'fresh_runtime_independent_reproduction': False, 'universal_theorem_verified': False, 'new_Lean': False, 'independent_review': False, 'steps': []}
try:
    outputs = []
    for copy in ('fresh_a', 'fresh_b'):
        folder = ROOT/copy
        folder.mkdir()
        raw = urllib.request.urlopen('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'+SOURCE+'/'+SCRIPT, timeout=45).read()
        if hashlib.sha256(raw).hexdigest() != EXPECTED:
            raise ValueError('Exact source bytes/hash mismatch')
        target = folder/'exact159.py'
        target.write_bytes(raw)
        (ev/(copy+'-source.py')).write_bytes(raw)
        for mode, flags in (('normal', []), ('optimized', ['-O'])):
            label = copy+'-'+mode
            stepclock = time.monotonic()
            result = subprocess.run([sys.executable, *flags, str(target)], cwd=folder, capture_output=True, timeout=240)
            for suffix, value in (('stdout.txt', result.stdout), ('stderr.txt', result.stderr), ('exit.txt', (str(result.returncode)+'\n').encode())):
                (ev/(label+'.'+suffix)).write_bytes(value)
            report['steps'].append({'label': label, 'exit_code': result.returncode, 'seconds': time.monotonic()-stepclock})
            if result.returncode != 0:
                raise ValueError(label+' failed; retained stdout/stderr')
            row = json.loads(result.stdout)
            if row.get('status') != 'EXACT_FINITE_DIAGNOSTICS_PASS' or row.get('rejected_mutations') != 10 or len(row.get('fixtures', [])) != 2:
                raise ValueError('Explicit diagnostic acceptance fields mismatch')
            outputs.append(result.stdout)
    if len(outputs) != 4 or any(x != outputs[0] for x in outputs):
        raise ValueError('Normal/-O or fresh-source-copy payload mismatch')
    report.update(status='EXACT_FINITE_DIAGNOSTICS_PASS', payload_sha256=hashlib.sha256(outputs[0]).hexdigest(), payload=json.loads(outputs[0]), normal_optimized_byte_identical=True, source_copies=2, process_replays=4)
except Exception:
    report['status'] = 'FAILED_PRESERVED'
    (ev/'failure.txt').write_text(traceback.format_exc())
finally:
    report['finished_utc'] = datetime.now(timezone.utc).isoformat()
    report['elapsed_seconds'] = time.monotonic()-clock
    report['child_maxrss_kib'] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    report['compute_units_billed'] = None
    (ev/'report.json').write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
    manifest = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(ev.iterdir()) if p.is_file()}
    (ev/'manifest.json').write_text(json.dumps(manifest, sort_keys=True, indent=2)+'\n')
    bundle = ROOT/'evidence159.zip'
    with zipfile.ZipFile(bundle, 'w', zipfile.ZIP_DEFLATED) as z:
        for p in sorted(ev.iterdir()):
            z.write(p, p.name)
    print('FINAL_REPORT159='+json.dumps(report, sort_keys=True))
    print('BUNDLE159_SHA256='+hashlib.sha256(bundle.read_bytes()).hexdigest())
    print('EVIDENCE159_BASE64='+base64.b64encode(bundle.read_bytes()).decode())
    if report['status'] != 'EXACT_FINITE_DIAGNOSTICS_PASS':
        raise RuntimeError('Diagnostics failed; full evidence preserved')
