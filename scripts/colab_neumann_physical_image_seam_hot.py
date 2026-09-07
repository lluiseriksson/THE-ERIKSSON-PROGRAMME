"""Bounded diagnostic AFTER independent verification of the retained cold parent.

Not a cold seal. No clone, CI or credentials. Explicit incremental summability prerequisite.
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

SOURCE = '970356bfc58ec2ca9ba94163be952d382c0689c9'
BASE = '108f30f954e3d807f16c4264fac56f4814c65ea4'
PIN = 'c84ea4829b1ddb13384c969edb8867bbb12007cb683b71335ef6830cef300464'
REV = 'neumann-physical-image-seam-hot-v1'
ROOT = Path('/content/hrpoly-neumann-boundary-orbit-diagnostic-v2')
PARENT = Path(str(ROOT) + '-evidence.tar.gz')
HELPERS = Path('/content/orbit-diagnostic-v2-launch')
OUT = Path('/content/' + REV)
NAMES = {'YangMills.RG.neumannActualFullGreenImage_summable_boundaryInvariant',
         'YangMills.RG.neumannActualFullGreenImage_lowerGhost',
         'YangMills.RG.neumannActualFullGreenImage_upperGhost'}

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--parent-sha256', required=True)
    parser.add_argument('--transfer-sha256', required=True)
    args = parser.parse_args()
    assert not OUT.exists(), 'NO_REEXECUTION'
    OUT.mkdir()
    records, audits, outputs = [], {}, {}
    status, error = 'FAIL', None
    env = os.environ.copy()

    def run(stage, command, timeout=120):
        start = time.perf_counter()
        timed = False
        with (OUT / (stage + '.log')).open('xb') as stream:
            p = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream,
                stderr=subprocess.STDOUT, start_new_session=True)
            print('STAGE=' + stage + ' PID=' + str(p.pid), flush=True)
            try:
                code = p.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed = True
                os.killpg(p.pid, signal.SIGKILL)
                code = p.wait()
        blob = (OUT / (stage + '.log')).read_bytes()
        record = dict(stage=stage, command=command, cwd=str(ROOT), exit=code,
            seconds=time.perf_counter()-start, timed_out=timed,
            timeout_seconds=timeout, log_sha256=sha(blob))
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
        def verified_reader(name, digest):
            url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/' + SOURCE + '/scripts/' + name + '.py'
            with urllib.request.urlopen(url, timeout=60) as response:
                blob = response.read()
            assert sha(blob) == digest, 'READER_HASH=' + name
            module = types.ModuleType(name)
            exec(compile(blob, name, 'exec'), module.__dict__)
            return module

        def parent_archive(rev, digest):
            raw = Path('/content/' + rev + '.tar.gz').read_bytes()
            assert sha(raw) == digest.lower(), 'PARENT_HASH=' + rev
            prefix = rev + '/'
            files = reader.unpack(raw)
            assert all(n.startswith(prefix) for n in files), 'PARENT_PREFIX'
            return {n[len(prefix):]:v for n,v in files.items()}

        image_reader = verified_reader('verify_neumann_boundary_image_hot',
            '69595e794145477bbbe1898814b9f23a2d05c029a0d41aba689612b6b9ace39f')
        image_files = parent_archive('neumann-boundary-image-hot-v1',
            '684302b7267d246c5d2594ae345f734fb537cadc4f091732f430e41f60dd1e9d')
        image_report = image_reader.verify(image_files, parent_report, args.parent_sha256, gate)
        series_reader = verified_reader('verify_neumann_boundary_series_hot',
            '32dccb3666dcd5e29a35f701f9eb4bbcfb3fcc6902915716334384bf8b9a21fd')
        series_files = parent_archive('neumann-boundary-series-hot-v2',
            'de851585e93f20a82b242512f9ffe6e33ae22ed12fc3ec5c1360bf1c34db3426')
        series_report = series_reader.verify(series_files, parent_report,
            args.parent_sha256, gate, image_report)
        transfer_reader = verified_reader('verify_neumann_physical_transfer_hot',
            'a66c36a0095f9fde006b5111bde2fce31846f004479c61776b08271f851e119d')
        transfer_files = parent_archive('neumann-physical-transfer-hot-v1', args.transfer_sha256)
        transfer_report = transfer_reader.verify(transfer_files, parent_report,
            args.parent_sha256, gate)
        reviews = dict(image=image_report, series=series_report, transfer=transfer_report,
            transfer_archive_sha256=args.transfer_sha256.lower())
        (OUT / 'dependency-reviews.json').write_text(json.dumps(reviews, sort_keys=True)+'\n')
        for name, files, report in [
            ('NeumannBoundaryImagePermutationDraft', image_files, image_report),
            ('NeumannBoundaryImageSeriesReindexDraft', series_files, series_report),
            ('NeumannPhysicalBoundaryTransferDraft', transfer_files, transfer_report)]:
            blob = files['orbit.olean']
            assert sha(blob) == report['output_sha256'], 'PARENT_OUTPUT=' + name
            destination = ROOT / '.lake/build/lib/lean' / (name + '.olean')
            if destination.exists():
                assert destination.read_bytes() == blob, 'PARENT_OUTPUT_MISMATCH=' + name
            else:
                destination.write_bytes(blob)
        bins = list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
        assert len(bins) == 1, 'TOOLCHAIN_LOCATION'
        env['PATH'] = str(bins[0].parent) + ':' + env['PATH']
        assert run('head', ['git', 'rev-parse', 'HEAD']).strip() == BASE
        assert run('mathlib', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']).strip() == reader.MATHLIB
        run('clean_before', ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        for exe in ('lean', 'lake'):
            assert '4.29.0-rc6' in run(exe+'_version', [exe, '--version'])
        source_name = 'NeumannPhysicalImageSeamDraft.lean'
        url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/' + SOURCE + '/tmp/' + source_name
        with urllib.request.urlopen(url, timeout=60) as response:
            blob = response.read()
        assert sha(blob) == PIN, 'SOURCE_BLOB'
        (OUT / source_name).write_bytes(blob)
        scratch = ROOT / 'tmp' / REV
        scratch.mkdir(exist_ok=False)
        source = scratch / source_name
        source.write_bytes(blob)
        # Summability stays an explicit analytic prerequisite, not an assumption.
        run('summability_prerequisite', ['lake', 'build',
            'YangMills.RG.NeumannActualFullGreenReflectionSummability'], timeout=3600)
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
            parent_archive_sha256=args.parent_sha256.lower(),
            transfer_archive_sha256=args.transfer_sha256.lower(), records=records,
            names=sorted(NAMES), audits=audits, outputs=outputs), sort_keys=True)+'\n')
        archive = Path(str(OUT) + '.tar.gz')
        with tarfile.open(archive, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(archive) + ' SHA256=' + sha(archive.read_bytes()), flush=True)
    return 0 if status == 'PASS' else 1

if __name__ == '__main__':
    raise SystemExit(main())


