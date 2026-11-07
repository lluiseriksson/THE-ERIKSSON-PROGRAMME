"""Thread-owned CPU Colab reproduction; prepared while disconnected."""
import base64
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import resource
import socket
import subprocess
import sys
import tempfile
import time
import zipfile

SOURCE = '1cf122830b459add773f235f024b8c8ff78d095c'
FILES = {
    'scripts/rectangular_gap180.py': 'bea744cb1c9a6dbc2e905c7b45bb1c9916bed410e88f672c28e60264d7593936',
    'docs/RECTANGULAR-FIXED-GAP-AND-ISOLATION-LIMIT-20261107.md': '09d936b2ada9b633d15516329a72eb964540905731f534cf329d232816853731',
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    require(platform.system() == 'Linux', 'Linux execution plane required')
    started = datetime.now(timezone.utc).isoformat()
    clock = time.monotonic()
    root = Path(tempfile.mkdtemp(prefix='tep-point180-'))
    out = root / 'evidence'
    out.mkdir()

    def run(label, command, cwd=None):
        child = subprocess.run(command, cwd=cwd, capture_output=True, check=False)
        (out / (label+'.stdout.txt')).write_bytes(child.stdout)
        (out / (label+'.stderr.txt')).write_bytes(child.stderr)
        temporary = out / (label+'.exit.tmp')
        temporary.write_text(str(child.returncode)+'\n')
        sentinel = out / (label+'.exit.txt')
        temporary.replace(sentinel)
        text = sentinel.read_text()
        require(text == str(child.returncode)+'\n', 'Exit sentinel readback')
        require(child.returncode == 0, label+' failed: '+child.stderr.decode(errors='replace')[-2000:])
        return child.stdout.decode()

    clones = []
    payloads = []
    for name in ('fresh_a', 'fresh_b'):
        clone = root / name
        run(name+'-clone', ['git', 'clone', '--filter=blob:none', '--no-checkout', '--depth=1',
                            'https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git', str(clone)])
        run(name+'-sparse-init', ['git', 'sparse-checkout', 'init', '--no-cone'], clone)
        run(name+'-sparse-set', ['git', 'sparse-checkout', 'set', '--no-cone', *('/'+p for p in FILES)], clone)
        run(name+'-fetch', ['git', 'fetch', '--depth=1', 'origin', SOURCE], clone)
        run(name+'-checkout', ['git', 'checkout', '--detach', SOURCE], clone)
        head = run(name+'-head', ['git', 'rev-parse', 'HEAD'], clone).strip()
        require(head == SOURCE, 'Pinned clone HEAD')
        status = run(name+'-status', ['git', 'status', '--porcelain', '--untracked-files=all'], clone)
        require(not status.strip(), 'Fresh source clone must be clean')
        for filename, expected in FILES.items():
            raw = (clone / filename).read_bytes()
            require(hashlib.sha256(raw).hexdigest() == expected, 'Source hash: '+filename)
            (out / (name+'-'+Path(filename).name)).write_bytes(raw)
        for mode, flags in (('normal', []), ('optimized', ['-O'])):
            target = out / (name+'-'+mode+'-payload.json')
            stdout = run(name+'-'+mode, [sys.executable, *flags,
                         str(clone/'scripts/rectangular_gap180.py'), '--output', str(target)], clone)
            require(stdout.strip() == 'FINITE_RECTANGLE_CHECKS_COMPLETE cases=12 rejected_mutations=5 solver_attacks=2', 'Finite check log')
            payloads.append(target.read_bytes())
        clones.append({'name': name, 'head': head, 'clean_before_execution': True,
                       'method': 'fresh filtered sparse git clone and pinned detached checkout'})
    require(len(payloads) == 4 and len(set(payloads)) == 1, 'Four ordinary/optimized payloads must match byte for byte')
    payload = json.loads(payloads[0])
    require(payload['case_count'] == 12 and payload['mutation_count'] == 5 and payload['solver_attack_count'] == 2, 'Expected actual check counts')
    report = {'unit': 180, 'started_utc': started, 'finished_utc': datetime.now(timezone.utc).isoformat(),
              'elapsed_seconds': time.monotonic()-clock, 'source': SOURCE, 'expected_git_LF_hashes': FILES,
              'clones': clones, 'matching_payloads': 4, 'normal_optimized_byte_identical': True,
              'payload_sha256': hashlib.sha256(payloads[0]).hexdigest(),
              'case_count': payload['case_count'], 'mutation_count': payload['mutation_count'],
              'child_maxrss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
              'host_fingerprint_sha256': hashlib.sha256(socket.gethostname().encode()).hexdigest(),
              'compute_units_billed': None, 'fresh_runtime_pair_completed': False,
              'all_size_theorem_computationally_certified': False, 'Lean_verified': False,
              'independent_review': False}
    (out/'report.json').write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
    manifest = [{'path': p.name, 'bytes': p.stat().st_size,
                 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
                for p in sorted(out.iterdir()) if p.is_file()]
    (out/'manifest.json').write_text(json.dumps(manifest, sort_keys=True, indent=2)+'\n')
    archive = root/'evidence180.zip'
    with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as z:
        for p in sorted(out.iterdir()):
            z.write(p, p.name)
    print('FINAL_REPORT180='+json.dumps(report, sort_keys=True))
    print('ARCHIVE180_SHA256='+hashlib.sha256(archive.read_bytes()).hexdigest())
    print('ARCHIVE180='+base64.b64encode(archive.read_bytes()).decode())


if __name__ == '__main__':
    main()
