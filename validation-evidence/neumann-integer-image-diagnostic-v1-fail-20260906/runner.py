"""One fresh diagnostic: Mathlib repro first, then actual source-importing draft.
No project-output restoration, no CI, no retries, no promotion or cold seal.
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
import neumann_integer_image_contract as C

RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'


def load(commit, path, expected, name):
    url = RAW + commit + '/' + path
    with urllib.request.urlopen(url, timeout=60) as response:
        blob = response.read()
    if C.sha(blob) != expected:
        raise RuntimeError('TRANSPORT_HASH=' + path)
    module = types.ModuleType(name)
    exec(compile(blob, url, 'exec'), module.__dict__)
    return module, blob


def main():
    base, _ = load(C.BASE_SHA, 'scripts/colab_cmp99_full_green_arbitrary_residue_cold.py',
                   C.BASE_WRAPPER_HASH, 'pinned_durable_base')
    gate, gate_blob = load(C.SOURCE, 'scripts/full_green_owner_exact_axiom_gate.py',
                           C.GATE_HASH, 'pinned_exact_gate')
    runner = base.runner
    runner.RUNNER_REV, runner.SOURCE_SHA, base.SOURCE = C.REV, C.SOURCE, C.SOURCE
    runner.ROOT, runner.EVIDENCE = Path(C.ROOT), Path(C.EVIDENCE)
    runner.ARCHIVE = Path(C.EVIDENCE + '.tar.gz')
    runner.PATH_MANIFEST = Path(C.ROOT + '-paths.txt')
    runner.SOURCE_BLOBS = C.BLOBS
    base.EXPECTED = frozenset(C.NAMES)
    runner.QUEUE = [(s, cmd, frozenset(C.NAMES) if s in
                     {'image_mathlib_repro', 'image_draft'} else None)
                    for s, cmd in C.COMMANDS.items()]

    def parse_axioms(output, expected):
        try:
            result = gate.exact_axioms(output, expected)
        except ValueError as exc:
            raise RuntimeError(str(exc)) from exc
        print('AXIOM_GATE=PASS ' + json.dumps(result, sort_keys=True), flush=True)

    runner.parse_axioms = base.parse_axioms = parse_axioms

    def run(stage, command, *, cwd=None):
        if stage not in {'image_mathlib_repro', 'image_draft'}:
            result = base.run(stage, command, cwd=cwd)
            if stage == 'cache_get':
                inputs = {p: (runner.ROOT / p).read_bytes() for p in C.BLOBS}
                repro = C.minimal_text(inputs)
                target = runner.ROOT / C.REPRO
                with target.open('xb') as stream:
                    stream.write(repro)
                (runner.EVIDENCE / 'mathlib-repro.lean').write_bytes(repro)
                print('MINIMAL_EXTRACTION_SHA256=' + C.sha(repro), flush=True)
            return result
        if any(r['stage'] == stage for r in runner.RECORDS):
            raise RuntimeError('DUPLICATE_STAGE')
        log = runner.EVIDENCE / (stage + '.log')
        start, timed_out = time.perf_counter(), False
        print('STAGE=' + stage + ' CMD=' + json.dumps(command), flush=True)
        with log.open('xb') as stream:
            child = subprocess.Popen(command, cwd=cwd, stdout=stream,
                                     stderr=subprocess.STDOUT, start_new_session=True)
            print('CHILD_PID=' + str(child.pid), flush=True)
            try:
                child.wait(timeout=120)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
        data = log.read_bytes()
        record = dict(stage=stage, command=command, cwd=str(cwd), exit=child.returncode,
                      seconds=time.perf_counter()-start, timed_out=timed_out,
                      log_file=log.name, output_sha256=C.sha(data))
        runner.RECORDS.append(record)
        temp = runner.EVIDENCE / (stage + '.json.tmp')
        temp.write_text(json.dumps(record, sort_keys=True) + '\n')
        temp.replace(runner.EVIDENCE / (stage + '.json'))
        print(data.decode(errors='replace'), flush=True)
        print(json.dumps(record, sort_keys=True), flush=True)
        if child.returncode or timed_out:
            raise RuntimeError('FIRST_ERROR=' + stage)
        return data.decode()

    runner.run = run
    original = runner.make_evidence

    def make_evidence(status, opened):
        runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
        (runner.EVIDENCE / 'runner.py').write_bytes(Path(__file__).read_bytes())
        (runner.EVIDENCE / 'contract.py').write_bytes(Path(C.__file__).read_bytes())
        (runner.EVIDENCE / 'full_green_owner_exact_axiom_gate.py').write_bytes(gate_blob)
        inputs = {}
        for path, digest in C.BLOBS.items():
            origin = runner.ROOT / path
            if origin.is_file():
                blob = origin.read_bytes()
                if C.sha(blob) != digest:
                    raise RuntimeError('FINAL_INPUT_HASH=' + path)
                name = Path(path).name
                (runner.EVIDENCE / name).write_bytes(blob)
                inputs[path] = dict(file=name, sha256=digest)
        outputs = {}
        for name in ('mathlib-repro.olean', 'image-draft.olean'):
            path = runner.EVIDENCE / name
            if path.is_file():
                outputs[name] = C.sha(path.read_bytes())
            elif status == 'PASS':
                raise RuntimeError('MISSING_OUTPUT=' + name)
        (runner.EVIDENCE / 'image-contract.json').write_text(json.dumps(dict(
            source=C.SOURCE, cold_seal=False, restored_project_outputs=False,
            inputs=inputs, outputs=outputs, names=sorted(C.NAMES),
            queue=list(C.COMMANDS), leaf_timeout_seconds=120,
            scope='integer image owner/indicator only; physical Q dictionary and inverse open'),
            sort_keys=True) + '\n')
        return original(status, opened)

    runner.make_evidence = make_evidence
    for path in (runner.ROOT, runner.EVIDENCE, runner.ARCHIVE,
                 runner.TOOLROOT, runner.ASSET):
        if path.exists():
            raise RuntimeError('FRESH_RUNTIME_REQUIRED_NO_REEXECUTION=' + str(path))
    gate.self_test()
    base.PREFLIGHT = base.preflight()
    from google.colab import runtime
    original_unassign = runtime.unassign
    runtime.unassign = lambda: print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    try:
        return runner.main()
    finally:
        runtime.unassign = original_unassign


if __name__ == '__main__':
    raise SystemExit(main())
