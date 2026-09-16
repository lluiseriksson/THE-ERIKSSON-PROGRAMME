"""One bounded HOT retry in retained v1 checkout; never a cold seal."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tarfile
import time
import types
import urllib.request

SOURCE = '8a0714a034be31c6f4f25243e1f1c2c2fc88431f'
DRAFT_HASH = '1077b61b5113678fa9cda799fafac904f2b302bdc7b67e342a342ebff96b8082'
REV = 'neumann-integer-image-hot-retry-v2'
ROOT = Path('/content/hrpoly-neumann-integer-image-counting-diagnostic-v1')
OLD = Path(str(ROOT) + '-evidence')
OUT = Path('/content/' + REV + '-evidence')
ARCHIVE = Path(str(OUT) + '.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def module(path, digest, name):
    blob = path.read_bytes()
    assert sha(blob) == digest, 'INSTRUMENT_PIN=' + name
    m = types.ModuleType(name)
    exec(compile(blob, str(path), 'exec'), m.__dict__)
    return m, blob


def main():
    assert not OUT.exists() and not ARCHIVE.exists(), 'NO_REEXECUTION'
    assert ROOT.is_dir() and OLD.is_dir(), 'RETAINED_RUNTIME_REQUIRED'
    OUT.mkdir()
    records, status, axioms, outputs = [], 'FAIL', {}, {}
    env = os.environ.copy()
    bins = list(Path('/content/lean-4.29.0-rc6-linux').glob('**/bin/lake'))
    assert len(bins) == 1, 'EXACT_TOOLCHAIN_BIN'
    env['PATH'] = str(bins[0].parent) + ':' + env['PATH']

    def run(stage, cmd, timeout=120):
        log = OUT / (stage + '.log')
        start, timed_out = time.perf_counter(), False
        with log.open('xb') as f:
            child = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=f,
                stderr=subprocess.STDOUT, start_new_session=True)
            print('STAGE=' + stage + ' PID=' + str(child.pid), flush=True)
            try:
                child.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
        b = log.read_bytes()
        r = dict(stage=stage, command=cmd, exit=child.returncode,
            seconds=time.perf_counter()-start, timed_out=timed_out,
            timeout_seconds=timeout, log_sha256=sha(b))
        records.append(r)
        temp = OUT / 'records.tmp'
        temp.write_text(json.dumps(records, sort_keys=True) + '\n')
        temp.replace(OUT / 'records.json')
        print(json.dumps(r, sort_keys=True), flush=True)
        print(b.decode(errors='replace')[-8000:], flush=True)
        if child.returncode or timed_out:
            raise RuntimeError('FIRST_ERROR=' + stage)
        return b.decode()

    try:
        C, cb = module(OLD / 'contract.py', 'fd53437cdfd46e31b9838055d04e4b21d1ae4a064bd1a6283406b318bc9784d5', 'old_contract')
        G, gb = module(OLD / 'full_green_owner_exact_axiom_gate.py', C.GATE_HASH, 'gate')
        (OUT / 'original-contract.py').write_bytes(cb)
        (OUT / 'axiom-gate.py').write_bytes(gb)
        G.self_test()
        assert run('base_head', ['git', 'rev-parse', 'HEAD']).strip() == C.SOURCE
        assert run('mathlib_pin', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']).strip() == '07642720480157414db592fa85b626dafb71355b'
        run('clean_before', ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', C.DRAFT, 'lean-toolchain', 'lake-manifest.json'])
        for exe in ('lean', 'lake'):
            assert '4.29.0-rc6' in run(exe + '_version', [exe, '--version'])
            (OUT / (exe + '-sha256.txt')).write_text(sha((bins[0].parent / exe).read_bytes()) + '\n')
        with urllib.request.urlopen(RAW + SOURCE + '/' + C.DRAFT, timeout=60) as response:
            draft = response.read()
        assert sha(draft) == DRAFT_HASH, 'NEW_SOURCE_HASH'
        inputs = {p: (ROOT / p).read_bytes() for p in C.BLOBS}
        assert all(sha(inputs[p]) == h for p, h in C.BLOBS.items()), 'BASE_SOURCE_PINS'
        inputs[C.DRAFT], C.BLOBS[C.DRAFT] = draft, DRAFT_HASH
        repro = C.minimal_text(inputs)
        for p, b in inputs.items():
            (OUT / Path(p).name).write_bytes(b)
        (OUT / 'mathlib-repro.lean').write_bytes(repro)
        (OUT / 'transport.json').write_text(json.dumps(dict(source=SOURCE,
            base=C.SOURCE, draft_sha256=DRAFT_HASH, input_pins=C.BLOBS,
            minimal_sha256=sha(repro), cold_seal=False), sort_keys=True) + '\n')
        rp = ROOT / ('tmp/' + REV + '-repro.lean')
        dp = ROOT / ('tmp/' + REV + '-draft.lean')
        for p, b in ((rp, repro), (dp, draft)):
            with p.open('xb') as f:
                f.write(b)
        for stage, p in (('mathlib_repro', rp), ('source_draft', dp)):
            if stage == 'source_draft':
                run('image_prerequisites', ['lake', 'build', 'YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra'], 1800)
            op = OUT / (stage + '.olean')
            text = run(stage, ['lake', 'env', 'lean', '-o', str(op), str(p)])
            axioms[stage] = G.exact_axioms(text, C.NAMES)
            assert op.stat().st_size > 0, 'MISSING_OUTPUT'
            outputs[op.name] = sha(op.read_bytes())
            print('AXIOM_GATE=PASS ' + stage, flush=True)
        run('clean_after', ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', C.DRAFT, 'lean-toolchain', 'lake-manifest.json'])
        status = 'PASS'
    except Exception as e:
        print('ERROR=' + repr(e), flush=True)
    finally:
        (OUT / 'runner.py').write_bytes(Path(__file__).read_bytes())
        (OUT / 'result.json').write_text(json.dumps(dict(status=status,
            source=SOURCE, cold_seal=False, records=records, axioms=axioms,
            outputs=outputs, runtime_retained=True), sort_keys=True) + '\n')
        with tarfile.open(ARCHIVE, 'w:gz') as t:
            t.add(OUT, arcname=OUT.name)
        print('FINAL_STATUS=' + status + ' COLD_SEAL=0', flush=True)
        print('ARCHIVE=' + str(ARCHIVE), flush=True)
        print('ARCHIVE_SHA256=' + sha(ARCHIVE.read_bytes()), flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
