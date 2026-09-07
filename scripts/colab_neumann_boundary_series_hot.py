"""Bounded diagnostic AFTER independent verification of the retained cold parent.

Not a cold seal. No clone, CI, credential, or dependency rebuild.
The parent archive hash must be supplied from the completed cold transcript.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import tarfile
import time
import types
import urllib.request

IMAGE_READER_HASH = '69595e794145477bbbe1898814b9f23a2d05c029a0d41aba689612b6b9ace39f'
SOURCE = '7800e4311399022e85c4a8b1f540c44551773f75'
BASE = '108f30f954e3d807f16c4264fac56f4814c65ea4'
PIN = 'e0f35dccf4635b18a8b8ea886f60aa0f7bf805a491ab7759350d1537b5d151d6'
REV = 'neumann-boundary-series-hot-v2'
ROOT = Path('/content/hrpoly-neumann-boundary-orbit-diagnostic-v2')
PARENT = Path(str(ROOT) + '-evidence.tar.gz')
HELPERS = Path('/content/orbit-diagnostic-v2-launch')
OUT = Path('/content/' + REV)
NAMES = {'YangMills.RG.neumannBoundaryImageIndexEquiv_factor',
         'YangMills.RG.neumannBoundaryImage_tsum_sum_reindex',
         'YangMills.RG.neumannBoundaryImage_reflected_source_sum'}

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--parent-sha256', required=True)
    args = parser.parse_args()
    assert not OUT.exists(), 'NO_REEXECUTION'
    OUT.mkdir()
    records, audits, outputs = [], {}, {}
    status, error = 'FAIL', None
    env = os.environ.copy()

    def run(stage, command):
        start = time.perf_counter()
        timed = False
        with (OUT / (stage + '.log')).open('xb') as stream:
            p = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream,
                stderr=subprocess.STDOUT, start_new_session=True)
            print('STAGE=' + stage + ' PID=' + str(p.pid), flush=True)
            try:
                code = p.wait(timeout=120)
            except subprocess.TimeoutExpired:
                timed = True
                os.killpg(p.pid, signal.SIGKILL)
                code = p.wait()
        blob = (OUT / (stage + '.log')).read_bytes()
        record = dict(stage=stage, command=command, cwd=str(ROOT), exit=code,
            seconds=time.perf_counter()-start, timed_out=timed,
            timeout_seconds=120, log_sha256=sha(blob))
        records.append(record)
        (OUT / (stage + '.json')).write_text(json.dumps(record, sort_keys=True)+'\n')
        print(blob.decode(errors='replace'), flush=True)
        assert code == 0 and not timed, 'FIRST_ERROR=' + stage
        return blob.decode()

    try:
        import sys
        sys.path.insert(0, str(HELPERS))
        reader_blob = (HELPERS / 'verify_neumann_boundary_orbit_diagnostic.py').read_bytes()
        assert sha(reader_blob) == '6ebfaeffc62b1b416007dc02fc101ff2e541feff58355523bbae80322809283a'
        helper_blob = (HELPERS / 'verify_neumann_counting_reflection_diagnostic_v2.py').read_bytes()
        assert sha(helper_blob) == 'a596e50eb708d39819da3f15557fa5705ab564874b70d9913f8a8b9794bec851'
        reader = types.ModuleType('parent_reader')
        exec(compile(reader_blob, 'parent_reader', 'exec'), reader.__dict__)
        raw = PARENT.read_bytes()
        assert sha(raw) == args.parent_sha256.lower()
        prefix = 'hrpoly-neumann-boundary-orbit-diagnostic-v2-evidence/'
        unpacked = reader.unpack(raw)
        assert all(n.startswith(prefix) for n in unpacked)
        parent_files = {n[len(prefix):]:v for n,v in unpacked.items()}
        parent_report = reader.verify(parent_files)
        (OUT / 'parent-review.json').write_text(json.dumps(parent_report, sort_keys=True)+'\n')
        gate = types.ModuleType('verified_gate')
        exec(compile(parent_files['axiom-gate.py'], 'verified_gate', 'exec'), gate.__dict__)
        # The image parent is hash-pinned, verified with its independent reader,
        # and only its verified output is installed into this HOT diagnostic.
        reader_url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/6448e892a9da085b6c7ee46e0dd3f74e74742726/scripts/verify_neumann_boundary_image_hot.py'
        with urllib.request.urlopen(reader_url, timeout=60) as response:
            image_reader_blob = response.read()
        image_reader = types.ModuleType('image_reader')
        # Reader identity is checked against the pinned Git blob by launcher.
        assert sha(image_reader_blob) == IMAGE_READER_HASH, 'IMAGE_READER_HASH'
        exec(compile(image_reader_blob, 'image_reader', 'exec'), image_reader.__dict__)
        image_raw = Path('/content/neumann-boundary-image-hot-v1.tar.gz').read_bytes()
        assert sha(image_raw) == '684302b7267d246c5d2594ae345f734fb537cadc4f091732f430e41f60dd1e9d'
        image_prefix = 'neumann-boundary-image-hot-v1/'
        image_unpacked = reader.unpack(image_raw)
        assert all(n.startswith(image_prefix) for n in image_unpacked)
        image_files = {n[len(image_prefix):]:v for n,v in image_unpacked.items()}
        image_report = image_reader.verify(image_files, parent_report, args.parent_sha256, gate)
        (OUT / 'image-parent-review.json').write_text(json.dumps(image_report, sort_keys=True)+'\n')
        output = image_files['orbit.olean']
        assert sha(output) == '46af4d92a85dc749828526631a7072832b2dc116b091784085451215e2b8dba4'
        destination = ROOT / '.lake/build/lib/lean/NeumannBoundaryImagePermutationDraft.olean'
        if destination.exists():
            assert destination.read_bytes() == output, 'PARENT_OUTPUT_MISMATCH'
        else:
            destination.write_bytes(output)
        bins = list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
        assert len(bins) == 1, 'TOOLCHAIN_LOCATION'
        env['PATH'] = str(bins[0].parent) + ':' + env['PATH']
        assert run('head', ['git', 'rev-parse', 'HEAD']).strip() == BASE
        assert run('mathlib', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']).strip() == reader.MATHLIB
        run('clean_before', ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        for exe in ('lean', 'lake'):
            assert '4.29.0-rc6' in run(exe+'_version', [exe, '--version'])
        source_name = 'NeumannBoundaryImageSeriesReindexDraft.lean'
        url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/' + SOURCE + '/tmp/' + source_name
        with urllib.request.urlopen(url, timeout=60) as response:
            blob = response.read()
        assert sha(blob) == PIN, 'SOURCE_BLOB'
        (OUT / source_name).write_bytes(blob)
        scratch = ROOT / 'tmp' / REV
        scratch.mkdir(exist_ok=False)
        source = scratch / source_name
        source.write_bytes(blob)
        # No lake build: a missing prerequisite is a recorded failure, not permission
        # to start another graph rebuild from this tiny diagnostic.
        text = run('orbit', ['lake', 'env', 'lean', '-o', str(OUT / 'orbit.olean'),
            str(source.relative_to(ROOT))])
        audits = gate.exact_axioms(text, NAMES)
        outputs['orbit.olean'] = sha((OUT / 'orbit.olean').read_bytes())
        run('clean_after', ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('ERROR=' + error, flush=True)
    finally:
        (OUT / 'runner.py').write_bytes(Path(__file__).read_bytes())
        (OUT / 'result.json').write_text(json.dumps(dict(status=status, error=error,
            source=SOURCE, base=BASE, pin=PIN, revision=REV, cold_seal=False,
            parent_archive_sha256=args.parent_sha256.lower(), records=records,
            names=sorted(NAMES), audits=audits, outputs=outputs), sort_keys=True)+'\n')
        archive = Path(str(OUT) + '.tar.gz')
        with tarfile.open(archive, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(archive) + ' SHA256=' + sha(archive.read_bytes()), flush=True)
    return 0 if status == 'PASS' else 1

if __name__ == '__main__':
    raise SystemExit(main())

