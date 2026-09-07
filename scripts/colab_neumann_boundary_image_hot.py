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

SOURCE = '7f7c6915a691d1b97bc53cfd695a978874e40a8e'
BASE = '108f30f954e3d807f16c4264fac56f4814c65ea4'
PIN = 'bf51447da311b0d6e98bc8286000418d40ad52721d3674dac2c493a654c596b7'
REV = 'neumann-boundary-image-hot-v1'
ROOT = Path('/content/hrpoly-neumann-boundary-orbit-diagnostic-v2')
PARENT = Path(str(ROOT) + '-evidence.tar.gz')
HELPERS = Path('/content/orbit-diagnostic-v2-launch')
OUT = Path('/content/' + REV)
NAMES = {'YangMills.RG.neumannBoundaryImageIndexEquiv_involutive',
         'YangMills.RG.neumannBoundaryImageIndexEquiv_image'}

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
        (OUT / 'parent-review.json').write_text(json.dumps(parent_report, sort_keys=True)+'\\n')
        gate = types.ModuleType('verified_gate')
        exec(compile(parent_files['axiom-gate.py'], 'verified_gate', 'exec'), gate.__dict__)
        bins = list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
        assert len(bins) == 1, 'TOOLCHAIN_LOCATION'
        env['PATH'] = str(bins[0].parent) + ':' + env['PATH']
        assert run('head', ['git', 'rev-parse', 'HEAD']).strip() == BASE
        assert run('mathlib', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']).strip() == reader.MATHLIB
        run('clean_before', ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        for exe in ('lean', 'lake'):
            assert '4.29.0-rc6' in run(exe+'_version', [exe, '--version'])
        source_name = 'NeumannBoundaryImagePermutationDraft.lean'
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


