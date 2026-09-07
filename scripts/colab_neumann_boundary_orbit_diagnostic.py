"""Fresh bounded retry of fixed-source boundary-orbit algebra.

V1 failed at a missing prerequisite before elaboration. This revision builds
that named prerequisite explicitly; the Lean source blob is unchanged.

Not a production cold seal. Exact input/output provenance and child exits
are retained; no regional inverse or scalar-window attainment is claimed.
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time
import types
import urllib.request

SOURCE = '108f30f954e3d807f16c4264fac56f4814c65ea4'
REV = 'neumann-boundary-orbit-diagnostic-v2'
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
BASE = 'ddf6fdc1882edddbf063389aab4d455a8ed30801'
BASE_HASH = '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
PINS = {'tmp/NeumannBoundaryOrbitPermutationRepro.lean':
    '8abe85a4e6bf901cb300026018d81e8ff93b7d78ae5ce1a39932d4436322b3e9'}
NAMES = {'orbit_repro': [
    'YangMills.RG.neumannBoundaryOrbitIndexEquiv_involutive',
    'YangMills.RG.neumannBoundaryOrbitIndexEquiv_image']}
SCOPE = 'fixed-source image-index permutation only; not seam, regional inverse, B0 or window15'

def load(ref, path, digest, name):
    url = RAW + ref + '/' + path
    blob = urllib.request.urlopen(url, timeout=60).read()
    assert hashlib.sha256(blob).hexdigest() == digest, 'TRANSPORT_HASH=' + path
    m = types.ModuleType(name)
    exec(compile(blob, url, 'exec'), m.__dict__)
    return m, blob

def main():
    base, base_blob = load(BASE, 'scripts/colab_cmp99_full_green_arbitrary_residue_cold.py', BASE_HASH, 'base')
    gate, gate_blob = load(SOURCE, 'scripts/full_green_owner_exact_axiom_gate.py', GATE_HASH, 'gate')
    r = base.runner
    r.RUNNER_REV, r.SOURCE_SHA, base.SOURCE = REV, SOURCE, SOURCE
    r.ROOT = Path('/content/hrpoly-' + REV)
    r.EVIDENCE = Path(str(r.ROOT) + '-evidence')
    r.ARCHIVE = Path(str(r.EVIDENCE) + '.tar.gz')
    r.PATH_MANIFEST = Path(str(r.ROOT) + '-paths.txt')
    r.SOURCE_BLOBS = PINS
    def run(stage, command, *, cwd=None):
        r.EVIDENCE.mkdir(parents=True, exist_ok=True)
        log = r.EVIDENCE / (stage + '.log')
        limit = 120 if stage in NAMES else 3600
        started, timed_out = time.perf_counter(), False
        print('STAGE=' + stage + ' CMD=' + json.dumps(command), flush=True)
        with log.open('xb') as stream:
            p = subprocess.Popen(command, cwd=cwd, env=os.environ.copy(),
                stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = p.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(p.pid, signal.SIGKILL)
                code = p.wait()
        blob = log.read_bytes()
        record = dict(stage=stage, command=command, cwd=str(cwd) if cwd else None,
            exit=code, seconds=time.perf_counter()-started, timed_out=timed_out,
            timeout_seconds=limit, log_file=log.name,
            output_sha256=hashlib.sha256(blob).hexdigest())
        r.RECORDS.append(record)
        temp = r.EVIDENCE / (stage + '.json.tmp')
        temp.write_text(json.dumps(record, sort_keys=True) + '\n')
        temp.replace(r.EVIDENCE / (stage + '.json'))
        output = blob.decode(errors='replace')
        print(output[-6000:], flush=True)
        print(json.dumps(record, sort_keys=True), flush=True)
        if code != 0 or timed_out:
            raise RuntimeError('FIRST_ERROR=' + stage)
        return output
    r.run = run
    lib = '.lake/build/lib/lean'
    r.QUEUE = [
        ("orbit_prerequisite", ["lake", "build",
            "YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra"], None),
        ("orbit_repro", ["lake", "env", "lean", "-o",
            ".lake/build/lib/lean/NeumannBoundaryOrbitPermutationRepro.olean",
            "tmp/NeumannBoundaryOrbitPermutationRepro.lean"], NAMES["orbit_repro"]),
        ("clean_after", ["git", "diff", "--exit-code", "HEAD", "--",
            "YangMills", "tmp/NeumannBoundaryOrbitPermutationRepro.lean",
            "lean-toolchain", "lake-manifest.json"], None),
    ]
    base.EXPECTED = frozenset().union(*NAMES.values())
    def parse(output, expected):
        try:
            result = gate.exact_axioms(output, expected)
        except ValueError as e:
            raise RuntimeError(str(e)) from e
        print('AXIOM_GATE=PASS ' + json.dumps(result, sort_keys=True), flush=True)
    r.parse_axioms = base.parse_axioms = parse
    previous = r.make_evidence
    def preserve(status, opened):
        r.EVIDENCE.mkdir(parents=True, exist_ok=True)
        for name, blob in [('runner.py', Path(__file__).read_bytes()), ('durable-base.py', base_blob), ('axiom-gate.py', gate_blob)]:
            (r.EVIDENCE / name).write_bytes(blob)
        outputs = {}
        for name in ["NeumannBoundaryOrbitPermutationRepro"]:
            f = r.ROOT / lib / (name + '.olean')
            if f.is_file():
                blob = f.read_bytes()
                outputs[f.name] = hashlib.sha256(blob).hexdigest()
                (r.EVIDENCE / f.name).write_bytes(blob)
        for p in PINS:
            f = r.ROOT / p
            if f.is_file():
                (r.EVIDENCE / f.name).write_bytes(f.read_bytes())
        (r.EVIDENCE / 'orbit-diagnostic-contract.json').write_text(json.dumps(dict(
            source=SOURCE, revision=REV, scope=SCOPE, cold_seal=False,
            pins=PINS, names={k: sorted(v) for k, v in NAMES.items()},
            queue=[(s,c,sorted(n) if n else None) for s,c,n in r.QUEUE], outputs=outputs,
            base=BASE, base_hash=BASE_HASH, gate_hash=GATE_HASH), sort_keys=True) + '\n')
        return previous(status, opened)
    r.make_evidence = preserve
    assert not any(p.exists() for p in (r.ROOT, r.EVIDENCE, r.ARCHIVE)), 'NO_REEXECUTION'
    gate.self_test()
    base.PREFLIGHT = base.preflight()
    from google.colab import runtime
    old = runtime.unassign
    runtime.unassign = lambda: print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    try:
        return r.main()
    finally:
        runtime.unassign = old

if __name__ == '__main__':
    raise SystemExit(main())


