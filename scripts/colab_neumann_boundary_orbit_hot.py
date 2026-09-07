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

SOURCE = '108f30f954e3d807f16c4264fac56f4814c65ea4'
BASE = '84ceb5f2f466ab8f4e9dea175fd412c7bf63a21e'
PIN = '8abe85a4e6bf901cb300026018d81e8ff93b7d78ae5ce1a39932d4436322b3e9'
REV = 'neumann-boundary-orbit-hot-v1'
ROOT = Path('/content/hrpoly-neumann-physical-reflection-promoted-cold-v1')
PARENT = Path(str(ROOT) + '-evidence.tar.gz')
HELPERS = Path('/content/neumann-physical-reflection-promoted-cold-v1-launch')
OUT = Path('/content/' + REV)
NAMES = {'YangMills.RG.neumannBoundaryOrbitIndexEquiv_involutive',
         'YangMills.RG.neumannBoundaryOrbitIndexEquiv_image'}

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
        # Verify the cold artifact before using its checkout or cached dependencies.
        reader_blob = (HELPERS / 'verify_neumann_physical_reflection_promoted_cold.py').read_bytes()
        assert sha(reader_blob) == 'c0d54f929d54f4d52ff94019f09ab3b9c70160755c8969b1a11faa0933985787'
        reader = types.ModuleType('cold_reader')
        exec(compile(reader_blob, 'cold_reader', 'exec'), reader.__dict__)
        old = reader.helper(HELPERS, 'verify_cmp99_full_green_residue_cold.py',
            '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')
        gate = reader.helper(HELPERS, 'full_green_owner_exact_axiom_gate.py', reader.GATE_HASH)
        old.PREFIX = 'hrpoly-' + reader.REV + '-evidence'
        parent_report = reader.verify(old.read_archive(PARENT, args.parent_sha256), gate, old)
        (OUT / 'parent-review.json').write_text(json.dumps(parent_report, sort_keys=True)+'\n')
        bins = list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
        assert len(bins) == 1, 'TOOLCHAIN_LOCATION'
        env['PATH'] = str(bins[0].parent) + ':' + env['PATH']
        assert run('head', ['git', 'rev-parse', 'HEAD']).strip() == BASE
        assert run('mathlib', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']).strip() == old.MATHLIB
        run('clean_before', ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        for exe in ('lean', 'lake'):
            assert '4.29.0-rc6' in run(exe+'_version', [exe, '--version'])
        source_name = 'NeumannBoundaryOrbitPermutationRepro.lean'
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
