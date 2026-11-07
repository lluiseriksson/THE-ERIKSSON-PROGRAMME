"""Prepared offline; UNEXECUTED. Reconcile189B before allocating own Linux CPU."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import platform
import resource
import subprocess
import tempfile
import time
import traceback
import zipfile

if platform.system() != 'Linux':
    raise RuntimeError('Own Colab Linux CPU required')

SHA = 'af96845bb3ce909d5cdef4c8f61fcbf73bababda'
BRANCH = 'codex/tep-detour-separation190-20261107'
FILES = {
    'scripts/detour_separation190.py': '581faf7f0719a6f1757ff69a014f1bc1656ec1776ea580a2b169d1e348144e38',
    'papers/flat-coarse-rank/research/2026-11-07_detour-separation190.txt':
        '1090cfb751ed667ca625f84003460279ac658df4a0caa839086e6c5eb489f23d',
}
root = Path(tempfile.mkdtemp(prefix='tep190-', dir='/content'))
ev = root/'evidence'
ev.mkdir()
tick = time.monotonic()
report = {'unit': 190, 'source_sha': SHA, 'started_utc': datetime.now(timezone.utc).isoformat(),
          'execution_plane': 'Own Colab Linux CPU', 'billed_units': None, 'steps': [],
          'payloads': [], 'independent_replication': False, 'all_size_proof': False,
          'formal_verification': False}


def run(args, label, cwd, timeout=240):
    begin = time.monotonic()
    child = subprocess.Popen(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    timed_out = False
    try:
        out, err = child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        child.kill()
        out, err = child.communicate()
    (ev/(label+'.stdout.txt')).write_bytes(out)
    (ev/(label+'.stderr.txt')).write_bytes(err)
    temp = ev/(label+'.exit.tmp')
    temp.write_text(str(child.returncode)+'\n')
    if temp.read_text().strip() != str(child.returncode):
        raise ValueError('Invalid actual exit sentinel')
    temp.replace(ev/(label+'.exit.txt'))
    report['steps'].append({'label': label, 'actual_exit': child.returncode,
                            'timed_out': timed_out, 'seconds': time.monotonic()-begin})
    if child.returncode or timed_out:
        raise RuntimeError(label+' failed; full logs retained')
    return out.decode().strip()


try:
    for name in ['fresh-a', 'fresh-b']:
        clone = root/name
        run(['git', 'clone', '--filter=blob:none', '--no-checkout', '--depth', '1',
             '--branch', BRANCH, 'https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git',
             str(clone)], name+'-clone', root)
        run(['git', 'sparse-checkout', 'set', '--no-cone']+['/'+p for p in FILES],
            name+'-sparse', clone)
        run(['git', 'checkout', '--detach', SHA], name+'-checkout', clone)
        if run(['git', 'rev-parse', 'HEAD'], name+'-head', clone) != SHA:
            raise ValueError('Wrong actual source checkout')
        for rel, digest in FILES.items():
            raw = (clone/rel).read_bytes()
            if hashlib.sha256(raw).hexdigest() != digest:
                raise ValueError('Wrong source bytes: '+rel)
            (ev/(name+'-'+Path(rel).name)).write_bytes(raw)
        for mode, args in [('normal', ['python3']), ('optimized', ['python3', '-O'])]:
            run(args+['scripts/detour_separation190.py'], name+'-'+mode, clone)
            raw = (clone/'payload190.json').read_bytes()
            obj = json.loads(raw)
            if (obj['positive_count'], obj['parity_count'], obj['mutation_count']) != (39, 9, 5):
                raise ValueError('Wrong acceptance counters')
            (ev/(name+'-'+mode+'-payload.json')).write_bytes(raw)
            report['payloads'].append({'clone': name, 'mode': mode,
                                      'sha256': hashlib.sha256(raw).hexdigest()})
    if len(report['payloads']) != 4 or len({p['sha256'] for p in report['payloads']}) != 1:
        raise ValueError('Fresh normal/optimized outputs differ')
    report['status'] = 'FINITE_DIAGNOSTICS_MATCHED_NOT_ALL_SIZE_PROOF'
except Exception:
    report['status'] = 'FAILED_PRESERVED'
    (ev/'failure.txt').write_text(traceback.format_exc())
finally:
    report.update(finished_utc=datetime.now(timezone.utc).isoformat(),
                  seconds=time.monotonic()-tick,
                  child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    (ev/'report190.json').write_text(json.dumps(report, indent=2)+'\n')
    manifest = [{'path': p.name, 'bytes': p.stat().st_size,
                 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(ev.iterdir())]
    (ev/'manifest190.json').write_text(json.dumps(manifest, indent=2)+'\n')
    bundle190 = Path('/content/tep190-evidence.zip')
    with zipfile.ZipFile(bundle190, 'w', zipfile.ZIP_DEFLATED) as z:
        for p in sorted(ev.iterdir()):
            z.write(p, p.name)
    print('REPORT190='+json.dumps(report))
    print('ZIP190_SHA256='+hashlib.sha256(bundle190.read_bytes()).hexdigest())
    print('ZIP190_BYTES='+str(bundle190.stat().st_size))
    print('ZIP190_PATH='+str(bundle190))
    # Do not stream a multi-megabyte base64 line into the notebook UI.
    # Export existing immutable bytes separately in bounded chunks after completion.
